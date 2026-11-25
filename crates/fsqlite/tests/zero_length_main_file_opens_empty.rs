//! A main database file of zero bytes is an empty database, as stock SQLite
//! opens it, under every open flag. A process killed while it creates a
//! database leaves exactly such a file beside the namespace sidecars it had
//! already written, and every later `SQLITE_OPEN_READ_ONLY` open, and every
//! `SQLITE_OPEN_READ_WRITE` open without `SQLITE_OPEN_CREATE`, answered
//! `CannotOpen` (0.4.13 and 9126990519). Stock opens it as an empty database:
//! no tables, `integrity_check` is `ok`, and a writable connection's first
//! write creates page 1.
//!
//! - `a_zero_byte_file_opens_as_an_empty_database_like_stock`: a zero-byte file
//!   with no sidecars, opened with each flag set.
//! - `a_crash_at_any_creation_step_leaves_what_stock_reads`: a child process
//!   creates a database (`journal_mode=WAL`, CREATE TABLE, INSERT, close) under
//!   strace and is SIGKILLed on entry to its Nth call of one store-file
//!   syscall, for every such call it makes: each write, sync, truncate,
//!   allocation, rename and unlink of the database or one of its sidecars. The
//!   call is faulted, so it never runs; the kernel keeps every write before
//!   it. The child creates by either route: `Connection::open_with_env`, the
//!   open behind a READ_WRITE|CREATE `open_with_flags`, or the identity-bound
//!   one a durable caller uses (`reserve_new_file`, then
//!   `open_reserved_with_expected_identity_and_env` under a strict
//!   multi-process env, with `synchronous=FULL`). The files left behind are
//!   opened with each flag set, and by the identity-bound existing open (which
//!   stock answers as READ_WRITE), by stock SQLite on a copy taken at once and
//!   by FrankenSQLite in place (the namespace record names the original file).
//!   Both must report the same outcome: the result code of a refused open or
//!   first read, otherwise the tables, the rows, whether `integrity_check` is
//!   `ok`, and for a writable open the result of one more write and the rows
//!   after it.
//!
//! The second test needs `strace` on PATH and permission to trace a child; it
//! fails, saying so, without them. Stores into the memory-mapped `-shm` are
//! not syscalls, so they are not kill points. Every data-path write must be a
//! syscall, which the discovery victim's io_uring counters check: a write
//! through the ring could not be killed at.

#![cfg(all(target_os = "linux", feature = "native"))]
#![recursion_limit = "512"]

use std::collections::{BTreeMap, BTreeSet};
use std::os::unix::process::ExitStatusExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use fsqlite::blocking::block_on;
use fsqlite::compat::{OpenFlags, open_with_flags_with_env};
use fsqlite::fsqlite_vfs::host_fs::{open_existing_regular_file_no_follow, reserve_new_file};
use fsqlite::{Connection, ConnectionEnv, FileIdentity, FrankenError};
use fsqlite_types::SqliteValue;

const CHILD_TEST: &str = "zero_length_child_process";
const CHILD_DB_ENV: &str = "FSQLITE_ZERO_LENGTH_CHILD_DB";
const CHILD_DONE_ENV: &str = "FSQLITE_ZERO_LENGTH_CHILD_DONE";
const CHILD_ROUTE_ENV: &str = "FSQLITE_ZERO_LENGTH_CHILD_ROUTE";
/// What the victim runs after its open; a kill point is any store-file
/// syscall from the open on.
const CREATE: [&str; 3] = [
    "PRAGMA journal_mode=WAL",
    "CREATE TABLE t(x INTEGER NOT NULL)",
    "INSERT INTO t VALUES (1)",
];
/// SQLITE_CANTOPEN, for an identity-bound open whose host file open fails
/// before the engine is reached.
const CANTOPEN: i32 = 14;

/// How the victim creates the database.
#[derive(Clone, Copy, Debug)]
enum Route {
    /// `Connection::open_with_env`, the open `open_with_flags(READ_WRITE |
    /// CREATE)` makes.
    Create,
    /// `reserve_new_file`, then `open_reserved_with_expected_identity_and_env`
    /// under a strict multi-process env, with `synchronous=FULL`.
    Reserved,
}

const ROUTES: [Route; 2] = [Route::Create, Route::Reserved];

impl Route {
    const fn name(self) -> &'static str {
        match self {
            Self::Create => "create",
            Self::Reserved => "reserved",
        }
    }
}

/// The env of a connection driven on its own thread, as `AsyncConnection`
/// and `fsqlite::blocking` open theirs; strict for identity-bound opens.
fn thread_env(strict: bool) -> ConnectionEnv {
    let mut env = ConnectionEnv::default();
    env.mark_blocking_io_inline_safe();
    env.set_strict_multi_process(strict);
    env
}

fn host_identity(file: &std::fs::File) -> FileIdentity {
    FileIdentity::from_file(file)
        .expect("descriptor identity")
        .expect("unix has a descriptor identity")
}

const KILL_SYSCALLS: [&str; 15] = [
    "write",
    "pwrite64",
    "writev",
    "pwritev",
    "pwritev2",
    "fsync",
    "fdatasync",
    "sync_file_range",
    "fallocate",
    "ftruncate",
    "rename",
    "renameat",
    "renameat2",
    "unlink",
    "unlinkat",
];
const TABLES: &str = "SELECT name FROM sqlite_master WHERE type = 'table' ORDER BY name";
const ROWS: &str = "SELECT x FROM t ORDER BY x";
const DEADLINE: Duration = Duration::from_secs(120);

#[derive(Clone, Copy, Debug)]
enum Mode {
    ReadOnly,
    ReadWrite,
    ReadWriteCreate,
    /// `open_existing_regular_file_no_follow`, then
    /// `open_existing_with_expected_identity_and_env` under a strict
    /// multi-process env; stock opens READ_WRITE.
    IdentityBound,
}

const MODES: [Mode; 4] = [
    Mode::ReadOnly,
    Mode::ReadWrite,
    Mode::ReadWriteCreate,
    Mode::IdentityBound,
];

impl Mode {
    fn frank(self) -> OpenFlags {
        match self {
            Self::ReadOnly => OpenFlags::SQLITE_OPEN_READ_ONLY,
            Self::ReadWrite | Self::IdentityBound => OpenFlags::SQLITE_OPEN_READ_WRITE,
            Self::ReadWriteCreate => {
                OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
            }
        }
    }

    fn stock(self) -> rusqlite::OpenFlags {
        match self {
            Self::ReadOnly => rusqlite::OpenFlags::SQLITE_OPEN_READ_ONLY,
            Self::ReadWrite | Self::IdentityBound => rusqlite::OpenFlags::SQLITE_OPEN_READ_WRITE,
            Self::ReadWriteCreate => {
                rusqlite::OpenFlags::SQLITE_OPEN_READ_WRITE
                    | rusqlite::OpenFlags::SQLITE_OPEN_CREATE
            }
        }
    }

    const fn writes(self) -> bool {
        !matches!(self, Self::ReadOnly)
    }
}

/// What one engine reports for one open of one file family.
#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    /// The open or one of its reads failed with this primary result code.
    Refused(i32),
    Opened {
        tables: Vec<String>,
        /// The values of `t`, an integer as its digits and anything else as
        /// its debug form.
        rows: Option<Vec<String>>,
        integrity_ok: bool,
        /// A writable open's one more write: the rows after it, or the
        /// primary result code that refused it.
        write: Option<Result<Vec<String>, i32>>,
    },
}

fn frank_code(error: &FrankenError) -> i32 {
    error.error_code() as i32
}

fn stock_code(error: &rusqlite::Error) -> i32 {
    match error {
        rusqlite::Error::SqliteFailure(failure, _) => failure.extended_code & 0xff,
        _ => -1,
    }
}

async fn frank_texts(conn: &fsqlite::Connection, sql: &str) -> Result<Vec<String>, FrankenError> {
    Ok(conn
        .query(sql)
        .await?
        .iter()
        .map(|row| match row.values() {
            [SqliteValue::Text(text)] => text.to_string(),
            other => format!("{other:?}"),
        })
        .collect())
}

async fn frank_rows(conn: &fsqlite::Connection) -> Result<Vec<String>, FrankenError> {
    Ok(conn
        .query(ROWS)
        .await?
        .iter()
        .map(|row| match row.values() {
            [SqliteValue::Integer(value)] => value.to_string(),
            other => format!("{other:?}"),
        })
        .collect())
}

async fn frank_write(conn: &fsqlite::Connection, has_t: bool) -> Result<Vec<String>, FrankenError> {
    if !has_t {
        conn.execute("CREATE TABLE t(x INTEGER NOT NULL)").await?;
    }
    conn.execute("INSERT INTO t VALUES (3)").await?;
    frank_rows(conn).await
}

async fn frank_open(db: &Path, mode: Mode) -> Result<Connection, Outcome> {
    let path = db.to_str().expect("utf-8 path");
    let refused = |error: FrankenError| Outcome::Refused(frank_code(&error));
    if let Mode::IdentityBound = mode {
        let file =
            open_existing_regular_file_no_follow(db).map_err(|_| Outcome::Refused(CANTOPEN))?;
        Connection::open_existing_with_expected_identity_and_env(
            path,
            host_identity(&file),
            thread_env(true),
        )
        .await
        .map_err(refused)
    } else {
        open_with_flags_with_env(path, mode.frank(), thread_env(false))
            .await
            .map_err(refused)
    }
}

async fn frank_opened(conn: Connection, mode: Mode) -> Result<Outcome, FrankenError> {
    let tables = frank_texts(&conn, TABLES).await?;
    let has_t = tables.iter().any(|table| table == "t");
    let rows = if has_t {
        Some(frank_rows(&conn).await?)
    } else {
        None
    };
    let integrity_ok = frank_texts(&conn, "PRAGMA integrity_check").await? == ["ok"];
    let write = if mode.writes() {
        Some(
            frank_write(&conn, has_t)
                .await
                .map_err(|error| frank_code(&error)),
        )
    } else {
        None
    };
    conn.close().await?;
    Ok(Outcome::Opened {
        tables,
        rows,
        integrity_ok,
        write,
    })
}

async fn frank_outcome(db: &Path, mode: Mode) -> Outcome {
    match frank_open(db, mode).await {
        Ok(conn) => frank_opened(conn, mode)
            .await
            .unwrap_or_else(|error| Outcome::Refused(frank_code(&error))),
        Err(refused) => refused,
    }
}

fn stock_texts(conn: &rusqlite::Connection, sql: &str) -> rusqlite::Result<Vec<String>> {
    let mut statement = conn.prepare(sql)?;
    let texts = statement
        .query_map([], |row| row.get::<_, String>(0))?
        .collect();
    texts
}

fn stock_rows(conn: &rusqlite::Connection) -> rusqlite::Result<Vec<String>> {
    let mut statement = conn.prepare(ROWS)?;
    let rows = statement
        .query_map([], |row| {
            Ok(match row.get::<_, rusqlite::types::Value>(0)? {
                rusqlite::types::Value::Integer(value) => value.to_string(),
                other => format!("{other:?}"),
            })
        })?
        .collect();
    rows
}

fn stock_write(conn: &rusqlite::Connection, has_t: bool) -> rusqlite::Result<Vec<String>> {
    if !has_t {
        conn.execute("CREATE TABLE t(x INTEGER NOT NULL)", [])?;
    }
    conn.execute("INSERT INTO t VALUES (3)", [])?;
    stock_rows(conn)
}

fn stock_opened(db: &Path, mode: Mode) -> rusqlite::Result<Outcome> {
    let conn = rusqlite::Connection::open_with_flags(db, mode.stock())?;
    let tables = stock_texts(&conn, TABLES)?;
    let has_t = tables.iter().any(|table| table == "t");
    let rows = if has_t {
        Some(stock_rows(&conn)?)
    } else {
        None
    };
    let integrity_ok = stock_texts(&conn, "PRAGMA integrity_check")? == ["ok"];
    let write = if mode.writes() {
        Some(stock_write(&conn, has_t).map_err(|error| stock_code(&error)))
    } else {
        None
    };
    conn.close().map_err(|(_, error)| error)?;
    Ok(Outcome::Opened {
        tables,
        rows,
        integrity_ok,
        write,
    })
}

fn stock_outcome(db: &Path, mode: Mode) -> Outcome {
    stock_opened(db, mode).unwrap_or_else(|error| Outcome::Refused(stock_code(&error)))
}

/// Copy every regular file of `db`'s directory into `into`, under the same
/// names, before either engine opens them.
fn copy_family(db: &Path, into: &Path) -> PathBuf {
    std::fs::create_dir_all(into).expect("copy directory");
    let dir = db.parent().expect("database directory");
    for entry in std::fs::read_dir(dir).expect("list the database directory") {
        let entry = entry.expect("directory entry");
        if entry.file_type().expect("file type").is_file() {
            std::fs::copy(entry.path(), into.join(entry.file_name()))
                .expect("copy a leftover file");
        }
    }
    into.join(db.file_name().expect("database name"))
}

/// Stock on a copy, then FrankenSQLite in place, of what `db`'s directory holds.
fn both_outcomes(db: &Path, copy_dir: &Path, mode: Mode) -> (Outcome, Outcome) {
    let copy = copy_family(db, copy_dir);
    let stock = stock_outcome(&copy, mode);
    let frank = block_on(frank_outcome(db, mode));
    (stock, frank)
}

/// The victim: creates the database and records that it finished. Exits
/// without running destructors. It is driven as `AsyncConnection`'s worker
/// thread and `fsqlite::blocking` drive a connection, on its own thread with
/// no async runtime, so its page writes are syscalls.
#[test]
fn zero_length_child_process() {
    let Ok(db) = std::env::var(CHILD_DB_ENV) else {
        return;
    };
    let done = PathBuf::from(std::env::var(CHILD_DONE_ENV).expect("the child's done file"));
    let route = std::env::var(CHILD_ROUTE_ENV).expect("the child's route");
    block_on(async {
        let (conn, reservation) = if route == Route::Reserved.name() {
            let reservation = reserve_new_file(Path::new(&db)).expect("reserve the database file");
            let conn = Connection::open_reserved_with_expected_identity_and_env(
                db.as_str(),
                host_identity(&reservation),
                thread_env(true),
            )
            .await
            .expect("initialize the reserved database");
            conn.execute("PRAGMA synchronous=FULL")
                .await
                .expect("PRAGMA synchronous=FULL");
            (conn, Some(reservation))
        } else {
            assert_eq!(route, Route::Create.name(), "unknown route");
            let conn = Connection::open_with_env(db.as_str(), thread_env(false))
                .await
                .expect("create the database");
            (conn, None)
        };
        for sql in CREATE {
            conn.execute(sql).await.expect(sql);
        }
        conn.close().await.expect("close the database");
        drop(reservation);
        // The data-path counters are process-global; a memory connection
        // reads them without touching the database family.
        let stats = Connection::open(":memory:")
            .await
            .expect("stats connection");
        let rows = stats
            .query("PRAGMA fsqlite.io_uring_stats")
            .await
            .expect("PRAGMA fsqlite.io_uring_stats");
        // A counter the pragma lacks is reported as `missing`, which the
        // parent's check refuses.
        let counter = |name: &str| {
            rows.iter()
                .find_map(|row| match row.values() {
                    [key, value] if key.as_text() == Some(name) => value.as_integer(),
                    _ => None,
                })
                .map_or_else(|| "missing".to_owned(), |value| value.to_string())
        };
        let report = format!(
            "ring_writes={} unix_fallbacks={}\n",
            counter("write_samples_total"),
            counter("unix_fallbacks_total")
        );
        stats.close().await.expect("close the stats connection");
        std::fs::write(&done, report).expect("write the done file");
    });
    std::process::exit(0);
}

/// The victim's done file: `(ring writes, unix fallbacks)`, or `None` when it
/// lacks either.
fn data_path_counters(done: &str) -> Option<(i64, i64)> {
    let field = |name: &str| {
        done.split_whitespace()
            .find_map(|pair| pair.strip_prefix(name)?.strip_prefix('=')?.parse().ok())
    };
    Some((field("ring_writes")?, field("unix_fallbacks")?))
}

struct Victim {
    status: String,
    killed: bool,
    /// The done file, which only a victim that finished writes.
    done: Option<String>,
    stderr: String,
}

impl Victim {
    const fn created(&self) -> bool {
        self.done.is_some()
    }
}

/// Run the victim on `db` by `route` under
/// `strace -f -qq -y -o trace <strace_args>`.
fn run_victim(route: Route, db: &Path, trace: &Path, strace_args: &[String]) -> Victim {
    let done = trace.with_extension("done");
    let stderr = trace.with_extension("stderr");
    let mut child = Command::new("strace")
        .args(["-f", "-qq", "-y", "-s", "256", "-o"])
        .arg(trace)
        .args(strace_args)
        .arg("--")
        .arg(std::env::current_exe().expect("test binary path"))
        .args(["--exact", CHILD_TEST, "--nocapture", "--test-threads=1"])
        .env(CHILD_DB_ENV, db)
        .env(CHILD_DONE_ENV, &done)
        .env(CHILD_ROUTE_ENV, route.name())
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(std::fs::File::create(&stderr).expect("victim stderr file"))
        .spawn()
        .expect("spawn strace (strace must be on PATH)");
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("wait for the victim") {
            break Some(status);
        }
        if started.elapsed() > DEADLINE {
            child.kill().ok();
            child.wait().ok();
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    Victim {
        status: status.map_or_else(
            || format!("timeout after {DEADLINE:?}"),
            |status| format!("{status}"),
        ),
        killed: status.is_some_and(|status| status.signal() == Some(9)),
        done: std::fs::read_to_string(&done).ok(),
        stderr: std::fs::read_to_string(&stderr).unwrap_or_default(),
    }
}

/// The suffix after `db` of every database-family path a file syscall names.
/// Pid-scoped temporary names cannot be filtered on before a victim runs.
fn family_suffixes(trace: &Path, db: &Path) -> BTreeSet<String> {
    let text = std::fs::read_to_string(trace).expect("discovery trace");
    let prefix = format!("\"{}", db.display());
    let mut suffixes = BTreeSet::new();
    for line in text.lines() {
        let mut rest = line;
        while let Some(at) = rest.find(&prefix) {
            let tail = &rest[at + prefix.len()..];
            let end = tail.find('"').unwrap_or(tail.len());
            if !tail[..end].contains(".tmp.") {
                suffixes.insert(tail[..end].to_owned());
            }
            rest = &tail[end..];
        }
    }
    suffixes
}

/// Per syscall, the descriptor path of each call per thread the trace starts.
fn calls_by_thread(trace: &Path) -> BTreeMap<String, BTreeMap<u32, Vec<String>>> {
    let text = std::fs::read_to_string(trace).expect("calibration trace");
    let mut calls: BTreeMap<String, BTreeMap<u32, Vec<String>>> = BTreeMap::new();
    for line in text.lines() {
        let Some((tid, call)) = line.split_once(' ') else {
            continue;
        };
        let Ok(tid) = tid.parse::<u32>() else {
            continue;
        };
        let Some((name, args)) = call.trim_start().split_once('(') else {
            continue;
        };
        if KILL_SYSCALLS.contains(&name) {
            let path = args
                .split_once('<')
                .and_then(|(_, rest)| rest.split_once('>'))
                .map_or_else(String::new, |(path, _)| path.to_owned());
            calls
                .entry(name.to_owned())
                .or_default()
                .entry(tid)
                .or_default()
                .push(path);
        }
    }
    calls
}

#[test]
fn a_zero_byte_file_opens_as_an_empty_database_like_stock() {
    if std::env::var_os(CHILD_DB_ENV).is_some() {
        return;
    }
    let mut mismatches = Vec::new();
    for mode in MODES {
        let dir = tempfile::tempdir().expect("tempdir");
        let db = dir.path().join("live").join("empty.db");
        std::fs::create_dir_all(db.parent().expect("parent")).expect("live directory");
        std::fs::write(&db, b"").expect("zero-byte file");
        let (stock, frank) = both_outcomes(&db, &dir.path().join("stock"), mode);
        let expected = Outcome::Opened {
            tables: Vec::new(),
            rows: None,
            integrity_ok: true,
            write: mode.writes().then(|| Ok(vec!["3".to_owned()])),
        };
        assert_eq!(
            stock, expected,
            "{mode:?}: stock reads a zero-byte file as an empty database"
        );
        if frank != stock {
            mismatches.push(format!(
                "{mode:?}: stock {stock:?}, FrankenSQLite {frank:?}"
            ));
        }
    }
    assert!(mismatches.is_empty(), "{mismatches:#?}");
}

#[test]
fn a_crash_at_any_creation_step_leaves_what_stock_reads() {
    if std::env::var_os(CHILD_DB_ENV).is_some() {
        return;
    }
    let probe = Command::new("strace").arg("-V").output();
    assert!(
        probe.as_ref().is_ok_and(|output| output.status.success()),
        "this test needs strace on PATH: {probe:?}"
    );
    let root = tempfile::tempdir().expect("tempdir");
    let root = std::fs::canonicalize(root.path()).expect("canonical tempdir");
    let mut mismatches = Vec::new();
    let mut compared = 0_usize;
    for route in ROUTES {
        let (route_compared, route_zero_length) = compare_route(&root, route, &mut mismatches);
        assert!(
            route_zero_length > 0,
            "{route:?}: no kill point left a zero-length main file, so this test no longer reaches the case it covers"
        );
        compared += route_compared;
    }
    assert!(
        mismatches.is_empty(),
        "{} of {compared} opens differ from stock: {mismatches:#?}",
        mismatches.len()
    );
}

/// Where stock reads its copy of a stage's `live/` files: beside `live/`.
fn stock_dir(db: &Path) -> PathBuf {
    db.parent()
        .and_then(Path::parent)
        .expect("stage directory")
        .join("stock")
}

/// Every kill point of one creation route, each read by every open mode.
/// Returns the opens compared and the kill points that left a zero-length
/// main file.
fn compare_route(root: &Path, route: Route, mismatches: &mut Vec<String>) -> (usize, usize) {
    let stage = |name: &str| -> PathBuf {
        let dir = root.join(route.name()).join(name);
        std::fs::create_dir_all(dir.join("live")).expect("stage directory");
        dir.join("live").join("c.db")
    };
    let trace_of = |name: &str| root.join(route.name()).join(format!("{name}.trace"));

    // The database-family paths the victim touches, for strace's path filter.
    let db = stage("discover");
    let trace = trace_of("discover");
    let found = run_victim(
        route,
        &db,
        &trace,
        &["-e".to_owned(), "trace=%file".to_owned()],
    );
    assert!(
        found.created(),
        "{route:?}: the discovery victim did not finish: {} {}",
        found.status,
        found.stderr
    );
    // Every data-path write was a syscall: a write through the ring is no
    // kill point. Fallbacks show the counters are live.
    let done = found.done.as_deref().unwrap_or_default();
    assert!(
        matches!(data_path_counters(done), Some((0, fallbacks)) if fallbacks > 0),
        "{route:?}: the victim must write only by syscall (no io_uring writes, some unix fallbacks): {done:?}"
    );
    let suffixes = family_suffixes(&trace, &db);
    let filter = |db: &Path| -> Vec<String> {
        suffixes
            .iter()
            .flat_map(|suffix| ["-P".to_owned(), format!("{}{suffix}", db.display())])
            .collect()
    };

    // The no-kill control: every kill point, and what both engines read.
    let db = stage("control");
    let trace = trace_of("control");
    let control = run_victim(route, &db, &trace, &filter(&db));
    assert!(
        control.created(),
        "{route:?}: the no-kill control did not finish: {} {}",
        control.status,
        control.stderr
    );
    let calls = calls_by_thread(&trace);
    let mut points = Vec::new();
    for (syscall, threads) in &calls {
        let most = threads.values().map(Vec::len).max().unwrap_or(0);
        points.extend((1..=most).map(|n| (syscall.clone(), n)));
    }
    assert!(
        !points.is_empty(),
        "{route:?}: the victim made no store-file syscall: {calls:?}"
    );
    let mut compared = 0;
    for mode in MODES {
        let name = format!("control-{mode:?}");
        let db = stage(&name);
        let victim = run_victim(route, &db, &trace_of(&name), &filter(&db));
        assert!(
            victim.created(),
            "{route:?} {name}: the victim did not finish: {}",
            victim.status
        );
        let (stock, frank) = both_outcomes(&db, &stock_dir(&db), mode);
        compared += 1;
        if frank != stock {
            mismatches.push(format!(
                "{route:?} {name}: stock {stock:?}, FrankenSQLite {frank:?}"
            ));
        }
    }

    let mut zero_length_leftovers = 0;
    for (syscall, n) in &points {
        for mode in MODES {
            let name = format!("{syscall}-{n}-{mode:?}");
            let db = stage(&name);
            let mut args = filter(&db);
            args.extend([
                "-e".to_owned(),
                format!("inject={syscall}:error=EIO:signal=KILL:when={n}"),
            ]);
            let victim = run_victim(route, &db, &trace_of(&name), &args);
            assert!(
                victim.killed && !victim.created(),
                "{route:?} {name}: the victim was not killed at its kill point: {} {}",
                victim.status,
                victim.stderr
            );
            if std::fs::metadata(&db).is_ok_and(|metadata| metadata.len() == 0) {
                zero_length_leftovers += 1;
            }
            let (stock, frank) = both_outcomes(&db, &stock_dir(&db), mode);
            compared += 1;
            println!("{route:?} {name}: stock {stock:?}; FrankenSQLite {frank:?}");
            if frank != stock {
                mismatches.push(format!(
                    "{route:?} {name}: stock {stock:?}, FrankenSQLite {frank:?}"
                ));
            }
        }
    }
    (compared, zero_length_leftovers)
}
