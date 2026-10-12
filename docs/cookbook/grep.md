# `grep`: flags, env, color and real files

A small `grep` that shows:

- several flags, combined freely in clusters (`-inc`);
- a typed option with an environment fallback (`-m` and `GREP_MAX`);
- a relation (`--count` conflicts with `--line-number`);
- `Cli.color()` and a `Cli.Term` that colors the app's own output;
- a pure search core with laws, and file IO in `act`;
- grep's exit status convention: 0, 1 or 2.

```console
$ grep --help
Print lines that contain a pattern

Usage: grep [OPTIONS] <PATTERN> <FILE>...

Arguments:
  <PATTERN>              Text to search for
  <FILE>...              Files to search

Options:
  -i, --ignore-case      Match without regard to case
  -v, --invert-match     Print the lines that do not match
  -c, --count            Print only the number of matching lines per file
  -n, --line-number      Prefix each line with its line number
  -m, --max-count <NUM>  Stop after NUM matching lines in each file [env:
                         GREP_MAX]
      --color <WHEN>     When to use color [default: auto] [possible values:
                         auto, always, never]
  -h, --help             Print help
  -V, --version          Print version

Examples:
  Find TODOs, any case, with line numbers:
    $ grep -in todo src/*.bend
  Count lines that mention errors:
    $ grep -c error app.log

Exit status is 0 if a line was printed, 1 if none was, and 2 if a file could not
be read.
```

## `app.bend`

```python
# Purpose: grep, a search tool with flags, an env fallback, color and file IO.
# Expected output: the matching lines; exit 0, 1 or 2 as grep does.
# Run: bend main.bend -- -in todo app.bend
import Base
import cli@1.0.0.0/cli.bend as Cli

type Query is Data:
  Query{pattern: String, ignore_case: Bool, invert: Bool, max: Maybe<&2, U32>}

type Grep is Data:
  Grep{query: Query, files: List<&2, String>, count: Bool, numbers: Bool}

def cli() -> Cli.Cmd:
  Cli.cmd("grep", "Print lines that contain a pattern", [
    Cli.version("1.0.0"),
    Cli.arg("-i, --ignore-case", "Match without regard to case", []),
    Cli.arg("-v, --invert-match", "Print the lines that do not match", []),
    Cli.arg("-c, --count", "Print only the number of matching lines per file",
      [Cli.conflicts("line-number")]),
    Cli.arg("-n, --line-number", "Prefix each line with its line number", []),
    Cli.arg("-m, --max-count <NUM>", "Stop after NUM matching lines in each file",
      [Cli.as_u32(), Cli.env("GREP_MAX")]),
    Cli.color(),
    Cli.arg("<PATTERN>", "Text to search for", []),
    Cli.arg("<FILE>...", "Files to search", [Cli.as_file()]),
    Cli.example("grep -in todo src/*.bend", "Find TODOs, any case, with line numbers"),
    Cli.example("grep -c error app.log", "Count lines that mention errors"),
    Cli.after("Exit status is 0 if a line was printed, 1 if none was, and 2 if a file could not be read."),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(Grep):
  do Cli.Dec<Grep>:
    ignore_case : Bool <- Cli.flag(m, "ignore-case")
    invert : Bool <- Cli.flag(m, "invert-match")
    count : Bool <- Cli.flag(m, "count")
    numbers : Bool <- Cli.flag(m, "line-number")
    max : Maybe<&2, U32> <- Cli.u32_opt(m, "max-count")
    pattern : String <- Cli.str(m, "pattern")
    files : List<&2, String> <- Cli.strs(m, "file")
    return Grep{Query{pattern, ignore_case, invert, max}, files, count, numbers}

# Matching. Everything from here to `act` is pure, so laws can pin it.

type Line is Data:
  Line{n: Nat, text: String}

def fold(ignore_case: Bool, s: String) -> String:
  match ignore_case:
    case True{}:
      String.to_lower(s)
    case False{}:
      s

# The lines of a file; a final newline ends the last line, not a new one.
def drop_last(+lines: List<&2, String>) -> List<&2, String>:
  List.take(&2, String, lines, Nat.sub(List.length(&2, String, lines), 1n))

def split_lines(ended: Bool, text: String) -> List<&2, String>:
  match ended:
    case True{}:
      drop_last(String.lines(text))
    case False{}:
      String.lines(text)

def lines_of(+text: String) -> List<&2, String>:
  split_lines(String.ends_with(text, "\n"), text)

def number(lines: List<&2, String>, +n: Nat) -> List<&2, Line>:
  match lines:
    case Nil{}:
      []
    case text <> rest:
      Line{n, text} <> number(rest, (1n + n : Nat))

def kept(hit: Bool, l: Line, rest: List<&2, Line>) -> List<&2, Line>:
  match hit:
    case True{}:
      l <> rest
    case False{}:
      rest

def keep(lines: List<&2, Line>, +ignore_case: Bool, +invert: Bool,
    +pattern: String) -> List<&2, Line>:
  match lines:
    case Nil{}:
      []
    case l <> rest:
      match l:
        case Line{n, +text}:
          kept(Bool.xor(invert, String.contains(fold(ignore_case, text), pattern)),
            Line{n, text}, keep(rest, ignore_case, invert, pattern))

def upto(max: Maybe<&2, U32>, lines: List<&2, Line>) -> List<&2, Line>:
  match max:
    case None{}:
      lines
    case Some{k}:
      List.take(&2, Line, lines, U32.to_nat(k))

def search(q: Query, text: String) -> List<&2, Line>:
  match q:
    case Query{pattern, +ignore_case, invert, max}:
      upto(max, keep(number(lines_of(text), 1n), ignore_case, invert,
        fold(ignore_case, pattern)))

# Output.

def label(color: Bool, +prefix: String) -> String:
  match prefix:
    case SNil{}:
      ""
    case SCon{h, t}:
      (Cli.paint(color, [Cli.Magenta{}], SCon{h, t}) ++ ":" : String)

def num(color: Bool, numbers: Bool, n: Nat) -> String:
  match numbers:
    case True{}:
      (Cli.paint(color, [Cli.Green{}], Nat.show(n)) ++ ":" : String)
    case False{}:
      ""

def show(+color: Bool, +numbers: Bool, +head: String, lines: List<&2, Line>) -> String:
  match lines:
    case Nil{}:
      ""
    case l <> rest:
      match l:
        case Line{n, text}:
          (head ++ num(color, numbers, n) ++ text ++ "\n"
            ++ show(color, numbers, head, rest) : String)

def report(+color: Bool, count: Bool, numbers: Bool, prefix: String,
    +lines: List<&2, Line>) -> String:
  match count:
    case True{}:
      (label(color, prefix) ++ Nat.show(List.length(&2, Line, lines)) ++ "\n" : String)
    case False{}:
      show(color, numbers, label(color, prefix), lines)

# File IO: read a whole file as text, closing it on every branch.

def Text() -> Type:
  Result<&1, &1, U32 & String, String>

def read_done(got: File & Text()) -> IO(Text()):
  match got:
    case (file, r):
      do IO<Text()>:
        File.close(file)
        return r

def read_sized(file: File, size: Result<&1, &1, U32 & String, U32>) -> IO(Text()):
  match size:
    case Done{n}:
      IO.bind(File & Text(), Text(), File.read(file, n), read_done)
    case Fail{e}:
      do IO<Text()>:
        File.close(file)
        return Fail{e}

def read_size(got: File & Result<&1, &1, U32 & String, U32>) -> IO(Text()):
  match got:
    case (file, size):
      read_sized(file, size)

def read_open(r: Result<&1, &1, U32 & String, File>) -> IO(Text()):
  match r:
    case Done{file}:
      IO.bind(File & Result<&1, &1, U32 & String, U32>, Text(), File.size(file), read_size)
    case Fail{e}:
      IO.pure(Text(), Fail{e})

def read_all(path: String) -> IO(Text()):
  IO.bind(Result<&1, &1, U32 & String, File>, Text(), File.open(path, "r"), read_open)

# Searching files. The result is 0 (printed a line), 1 (none) or 2 (an error).

def found(+lines: List<&2, Line>) -> U32:
  Bool.pick(U32, List.is_empty(&2, Line, lines), 1, 0)

def emit(+out: String, code: U32) -> IO(U32):
  match out:
    case SNil{}:
      IO.pure(U32, code)
    case SCon{h, t}:
      do IO<U32>:
        IO.write(SCon{h, t})
        return code

def shown(color: Bool, count: Bool, numbers: Bool, prefix: String,
    +lines: List<&2, Line>) -> IO(U32):
  emit(report(color, count, numbers, prefix, lines), found(lines))

def one(color: Bool, q: Query, count: Bool, numbers: Bool, prefix: String,
    +path: String, r: Text()) -> IO(U32):
  match r:
    case Fail{(code, msg)}:
      do IO<U32>:
        IO.print_err(("grep: " ++ path ++ ": " ++ msg : String))
        return 2
    case Done{text}:
      shown(color, count, numbers, prefix, search(q, text))

def worst(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, Bool.or(U32.is_eq(a, 2), U32.is_eq(b, 2)), 2, U32.min(a, b))

def each(+color: Bool, +q: Query, +count: Bool, +numbers: Bool, +many: Bool,
    files: List<&2, String>, code: U32) -> IO(U32):
  match files:
    case Nil{}:
      IO.pure(U32, code)
    case +path <> rest:
      do IO<U32>:
        r : Text() <- read_all(path)
        c : U32 <- one(color, q, count, numbers, Bool.pick(String, many, path, ""), path, r)
        each(color, q, count, numbers, many, rest, worst(code, c))

def many(files: List<&2, String>) -> Bool:
  Nat.is_lt(1n, List.length(&2, String, files))

def act(+t: Cli.Term, g: Grep) -> IO(U32):
  match t:
    case Cli.Term{out_color, err_color, width}:
      match g:
        case Grep{query, +files, count, numbers}:
          each(out_color, query, count, numbers, many(files), files, 1)
```

Notes:

- **Decisions are pure.** `search` and `report` take text and return text,
  so laws pin every output format, colored or not. `act` only reads files and
  writes what `report` returns.
- **The record is shaped for its readers.** `Query` holds what `search`
  reads, and `act` passes `search` that record rather than the whole `Grep`.
- **Exit status.** grep uses 1 for "no lines", so a script can tell "no
  match" from failure, and 2 for errors, the same code the library uses for
  usage errors. `worst` keeps 2 if any file failed, otherwise 0 if any
  file matched.
- **Color.** `out_color` already reflects `--color`, `NO_COLOR`,
  `CLICOLOR_FORCE` and whether stdout is a terminal, so `grep todo a | less`
  is plain while `grep --color=always todo a | less -R` is colored
  ([Terminal output](../how-to/terminal.md)).
- **No stdin.** `<FILE>...` is required. Reading standard input needs a loop
  over `File.read` chunks, and a chunk boundary may split a UTF-8 character;
  until Base can decode bytes, read whole files with `File.size` and one
  `File.read`, as here.
- **Whole files in memory.** Each file is read at once; this is a teaching
  example, not a replacement for GNU grep on multi-gigabyte logs.

## `main.bend`

```python
# Purpose: the grep shell.
# Expected output: the matching lines; exit 0, 1 or 2 as grep does.
# Run: bend main.bend -- -in todo app.bend
import Base
import ./app.bend as App
import cli@1.0.0.0/run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Grep, ~App.decode, ~App.act, App.cli())
```

## `LAWS.bend`

```python
# Purpose: laws for grep: the definition, parsing, and the pure search core.
# Expected output: one TODO per law until PROOF.bend proves them.
# Run: bend LAWS.bend --check-only
import Base
import ./app.bend as App
import cli@1.0.0.0/cli.bend as Cli

law cli_ok:
  {Cli.check(~App.Grep, ~App.decode, App.cli()) == [] : List<&2, Cli.Problem>}

law cluster:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n), ["-inm2", "todo", "a", "b"])
    == Cli.Go{App.Grep{App.Query{"todo", True{}, False{}, Some{2}}, ["a", "b"], False{}, True{}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Grep>}

law max_from_env:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(),
      Cli.host_var(Cli.host(80n), "GREP_MAX", "5"), ["x", "a"])
    == Cli.Go{App.Grep{App.Query{"x", False{}, False{}, Some{5}}, ["a"], False{}, False{}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Grep>}

law count_and_numbers:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n), ["-c", "-n", "x", "a"])
    == Cli.Exit{2, "", "error: the argument '--line-number' cannot be used with '--count'\n\nUsage: grep [OPTIONS] <PATTERN> <FILE>...\n\nFor more information, try '--help'.\n"}
    : Cli.Step<App.Grep>}

law any_case:
  {App.search(App.Query{"todo", True{}, False{}, None{}}, "a TODO\nb\ntodo c\n")
    == [App.Line{1n, "a TODO"}, App.Line{3n, "todo c"}] : List<&2, App.Line>}

law invert_max:
  {App.search(App.Query{"x", False{}, True{}, Some{1}}, "x\ny\nz")
    == [App.Line{2n, "y"}] : List<&2, App.Line>}

law numbered:
  {App.report(False{}, False{}, True{}, "a.txt", [App.Line{3n, "hi"}])
    == "a.txt:3:hi\n" : String}

law counted:
  {App.report(False{}, True{}, False{}, "", [App.Line{1n, "a"}, App.Line{2n, "b"}])
    == "2\n" : String}

law colored:
  {App.report(True{}, False{}, True{}, "a", [App.Line{7n, "x"}])
    == "\u{1b}[35ma\u{1b}[0m:\u{1b}[32m7\u{1b}[0m:x\n" : String}

law exit_codes:
  {[App.worst(1, 0), App.worst(1, 1), App.worst(0, 2)] == [0, 1, 2] : List<&2, U32>}
```

## `PROOF.bend`

```python
# Purpose: proofs of the grep laws.
# Expected output: ALL PROOFS CHECK
# Run: bend PROOF.bend
import Base
import ./LAWS.bend as Laws

def Laws.cli_ok():
  {==}

def Laws.cluster():
  {==}

def Laws.max_from_env():
  {==}

def Laws.count_and_numbers():
  {==}

def Laws.any_case():
  {==}

def Laws.invert_max():
  {==}

def Laws.numbered():
  {==}

def Laws.counted():
  {==}

def Laws.colored():
  {==}

def Laws.exit_codes():
  {==}
```

## Running it

```console
$ bend main.bend -o grep
$ ./grep -in todo app.bend notes.txt
app.bend:1:fix: TODO later
app.bend:3:todo: tests
$ ./grep -c todo app.bend
1
$ ./grep zzz notes.txt
$ GREP_MAX=abc ./grep x notes.txt
error: invalid value 'abc' for '--max-count <NUM>' from environment variable GREP_MAX: expected a whole number from 0 to 4294967295

Usage: grep [OPTIONS] <PATTERN> <FILE>...

For more information, try '--help'.
$ ./grep x missing.txt notes.txt
grep: missing.txt: No such file or directory
```

Exit statuses, in order: 0, 0, 1, 2, 2.
