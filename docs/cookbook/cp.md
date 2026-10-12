# `cp`: many sources, one destination

A small `cp` that shows:

- a variadic positional before a required one (`<SRC>... <DEST>`);
- flags with short and long names;
- examples in help;
- a pure planning function with laws, and real file IO in `act` that closes
  every handle on every branch.

```console
$ cp --help
Copy files

Usage: cp [OPTIONS] <SRC>... <DEST>

Arguments:
  <SRC>...          Files to copy
  <DEST>            File to write, or a directory if there are several sources

Options:
  -n, --no-clobber  Do not overwrite an existing file
  -v, --verbose     Print each file as it is copied
  -h, --help        Print help
  -V, --version     Print version

Examples:
  Copy one file:
    $ cp notes.txt notes.bak
  Copy two files into backup/:
    $ cp a.txt b.txt backup
```

## `app.bend`

The definition, the decoder, the plan and `act`. Laws may import this file.

```python
# Purpose: cp, which copies files.
# Expected output: nothing on success; with -v, one line per file copied.
# Run: bend main.bend -- a.txt b.txt backup
import Base
import cli@1.0.0.0/cli.bend as Cli

type Target is Data:
  Target{from: String, to: String}

type Copy is Data:
  Copy{srcs: List<&2, String>, dest: String, no_clobber: Bool, verbose: Bool}

def cli() -> Cli.Cmd:
  Cli.cmd("cp", "Copy files", [
    Cli.version("1.0.0"),
    Cli.arg("-n, --no-clobber", "Do not overwrite an existing file", []),
    Cli.arg("-v, --verbose", "Print each file as it is copied", []),
    Cli.arg("<SRC>...", "Files to copy", [Cli.as_file()]),
    Cli.arg("<DEST>", "File to write, or a directory if there are several sources",
      [Cli.as_file()]),
    Cli.example("cp notes.txt notes.bak", "Copy one file"),
    Cli.example("cp a.txt b.txt backup", "Copy two files into backup/"),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(Copy):
  do Cli.Dec<Copy>:
    no_clobber : Bool <- Cli.flag(m, "no-clobber")
    verbose : Bool <- Cli.flag(m, "verbose")
    srcs : List<&2, String> <- Cli.strs(m, "src")
    dest : String <- Cli.str(m, "dest")
    return Copy{srcs, dest, no_clobber, verbose}

# The last path segment: base("x/y/a.txt") == "a.txt".
def base(+path: String) -> String:
  Maybe.default(&2, String, List.last(&2, String, String.split(path, '/')), path)

# Where each source goes.
def into(+dir: String, srcs: List<&2, String>) -> List<&2, Target>:
  match srcs:
    case Nil{}:
      []
    case +src <> rest:
      Target{src, (dir ++ "/" ++ base(src) : String)} <> into(dir, rest)

def targets(srcs: List<&2, String>, dest: String) -> List<&2, Target>:
  match srcs:
    case Nil{}:
      []
    case src <> rest:
      match rest:
        case Nil{}:
          [Target{src, dest}]
        case +r <> t:
          into(dest, src <> r <> t)

# File IO. Every handle is closed on every branch.

def Bytes() -> Type:
  Result<&1, &1, U32 & String, List<&2, U32>>

def read_done(got: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Bytes()):
  match got:
    case (file, r):
      do IO<Bytes()>:
        File.close(file)
        return r

def read_sized(file: File, size: Result<&1, &1, U32 & String, U32>) -> IO(Bytes()):
  match size:
    case Done{n}:
      IO.bind(File & Bytes(), Bytes(), File.read_bytes(file, n), read_done)
    case Fail{e}:
      do IO<Bytes()>:
        File.close(file)
        return Fail{e}

def read_size(got: File & Result<&1, &1, U32 & String, U32>) -> IO(Bytes()):
  match got:
    case (file, size):
      read_sized(file, size)

def read_open(r: Result<&1, &1, U32 & String, File>) -> IO(Bytes()):
  match r:
    case Done{file}:
      IO.bind(File & Result<&1, &1, U32 & String, U32>, Bytes(), File.size(file), read_size)
    case Fail{e}:
      IO.pure(Bytes(), Fail{e})

def read_all(path: String) -> IO(Bytes()):
  IO.bind(Result<&1, &1, U32 & String, File>, Bytes(), File.open(path, "r"), read_open)

def Saved() -> Type:
  Result<&1, &1, U32 & String, Unit>

def write_done(got: File & Saved()) -> IO(Saved()):
  match got:
    case (file, r):
      do IO<Saved()>:
        File.close(file)
        return r

def write_open(data: List<&2, U32>, r: Result<&1, &1, U32 & String, File>) -> IO(Saved()):
  match r:
    case Done{file}:
      IO.bind(File & Saved(), Saved(), File.write_bytes(file, data), write_done)
    case Fail{e}:
      IO.pure(Saved(), Fail{e})

def write_all(path: String, data: List<&2, U32>) -> IO(Saved()):
  IO.bind(Result<&1, &1, U32 & String, File>, Saved(), File.open(path, "w"),
    write_open(data))

def exists_open(r: Result<&1, &1, U32 & String, File>) -> IO(Bool):
  match r:
    case Done{file}:
      do IO<Bool>:
        File.close(file)
        return True{}
    case Fail{e}:
      IO.pure(Bool, False{})

def exists(path: String) -> IO(Bool):
  IO.bind(Result<&1, &1, U32 & String, File>, Bool, File.open(path, "r"), exists_open)

# Copying.

def fail(what: String, path: String, r: (U32 & String)) -> IO(U32):
  match r:
    case (code, msg):
      do IO<U32>:
        IO.print_err(("cp: cannot " ++ what ++ " '" ++ path ++ "': " ++ msg : String))
        return 1

def said(verbose: Bool, from: String, to: String) -> IO(U32):
  match verbose:
    case True{}:
      do IO<U32>:
        IO.print(("'" ++ from ++ "' -> '" ++ to ++ "'" : String))
        return 0
    case False{}:
      IO.pure(U32, 0)

def wrote(verbose: Bool, from: String, to: String, r: Saved()) -> IO(U32):
  match r:
    case Fail{e}:
      fail("write", to, e)
    case Done{u}:
      said(verbose, from, to)

def copy_read(verbose: Bool, from: String, +to: String, r: Bytes()) -> IO(U32):
  match r:
    case Fail{e}:
      fail("read", from, e)
    case Done{data}:
      IO.bind(Saved(), U32, write_all(to, data), wrote(verbose, from, to))

def copy_if(skip: Bool, verbose: Bool, +from: String, to: String) -> IO(U32):
  match skip:
    case True{}:
      IO.pure(U32, 0)
    case False{}:
      IO.bind(Bytes(), U32, read_all(from), copy_read(verbose, from, to))

def copy_one(no_clobber: Bool, verbose: Bool, from: String, +to: String) -> IO(U32):
  match no_clobber:
    case True{}:
      IO.bind(Bool, U32, exists(to), there => copy_if(there, verbose, from, to))
    case False{}:
      copy_if(False{}, verbose, from, to)

def copy_target(no_clobber: Bool, verbose: Bool, t: Target) -> IO(U32):
  match t:
    case Target{from, to}:
      copy_one(no_clobber, verbose, from, to)

def copy_all(+no_clobber: Bool, +verbose: Bool, ts: List<&2, Target>, code: U32) -> IO(U32):
  match ts:
    case Nil{}:
      IO.pure(U32, code)
    case t <> rest:
      do IO<U32>:
        c : U32 <- copy_target(no_clobber, verbose, t)
        copy_all(no_clobber, verbose, rest, U32.max(code, c))

def act(+t: Cli.Term, c: Copy) -> IO(U32):
  match c:
    case Copy{srcs, dest, no_clobber, verbose}:
      copy_all(no_clobber, verbose, targets(srcs, dest), 0)
```

Notes:

- **Slots.** `<SRC>...` comes before `<DEST>`, so the parser fills `DEST`
  from the last token and gives `SRC` the rest. With a single token, `DEST`
  takes it and `SRC` is missing ([Positionals](../how-to/positionals.md#cp-style-many-sources-one-destination)).
- **Plan, then act.** `targets` decides where every file goes and is pure,
  so laws pin it. `act` only performs the copies. This version treats
  `DEST` as a directory whenever there are several sources, and as a file
  name when there is one; a real `cp` would also check whether a single
  `DEST` is a directory.
- **Errors keep going.** A file that cannot be read or written prints
  `cp: cannot read '<path>': <reason>` and the copy continues with the next
  one; the exit code is the highest seen, so 1 if anything failed.
- **Bytes, not text.** `File.read_bytes` and `File.write_bytes` copy files
  that are not UTF-8 unchanged.
- **Ids.** `--no-clobber` has id `no-clobber`; `<SRC>...` has id `src`.

## `main.bend`

```python
# Purpose: cp, which copies files.
# Expected output: nothing on success; with -v, one line per file copied.
# Run: bend main.bend -- a.txt b.txt backup
import Base
import ./app.bend as App
import cli@1.0.0.0/run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Copy, ~App.decode, ~App.act, App.cli())
```

## `LAWS.bend`

```python
# Purpose: laws for cp: the definition is valid, files go where they should, and a
# lone argument is reported as a missing source.
# Expected output: one TODO per law until PROOF.bend proves them.
# Run: bend LAWS.bend --check-only
import Base
import ./app.bend as App
import cli@1.0.0.0/cli.bend as Cli

law cli_ok:
  {Cli.check(~App.Copy, ~App.decode, App.cli()) == [] : List<&2, Cli.Problem>}

law one_source:
  {App.targets(["notes.txt"], "notes.bak")
    == [App.Target{"notes.txt", "notes.bak"}] : List<&2, App.Target>}

law many_sources:
  {App.targets(["a.txt", "doc/b.txt"], "backup")
    == [App.Target{"a.txt", "backup/a.txt"}, App.Target{"doc/b.txt", "backup/b.txt"}]
    : List<&2, App.Target>}

law parse:
  {Cli.eval(~App.Copy, ~App.decode, App.cli(), Cli.host(80n), ["-v", "a", "b", "dir"])
    == Cli.Go{App.Copy{["a", "b"], "dir", False{}, True{}}, Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Copy>}

law lone_argument:
  {Cli.eval(~App.Copy, ~App.decode, App.cli(), Cli.host(80n), ["a"])
    == Cli.Exit{2, "", "error: the following required arguments were not provided:\n  <SRC>...\n\nUsage: cp [OPTIONS] <SRC>... <DEST>\n\nFor more information, try '--help'.\n"}
    : Cli.Step<App.Copy>}
```

## `PROOF.bend`

```python
# Purpose: proofs of the cp laws.
# Expected output: ALL PROOFS CHECK
# Run: bend PROOF.bend
import Base
import ./LAWS.bend as Laws

def Laws.cli_ok():
  {==}

def Laws.one_source():
  {==}

def Laws.many_sources():
  {==}

def Laws.parse():
  {==}

def Laws.lone_argument():
  {==}
```

## Running it

```console
$ bend main.bend -o cp
$ ./cp -v a.txt b.txt backup
'a.txt' -> 'backup/a.txt'
'b.txt' -> 'backup/b.txt'
$ ./cp -n a.txt b.txt backup
$ ./cp missing.txt x
cp: cannot read 'missing.txt': No such file or directory
$ ./cp a.txt
error: the following required arguments were not provided:
  <SRC>...

Usage: cp [OPTIONS] <SRC>... <DEST>

For more information, try '--help'.
```

The last two exit 1 and 2. The second copies nothing, because both
targets exist.
