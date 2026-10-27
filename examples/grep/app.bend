# Purpose: the grep example app: a flag, an option read from argv or the
# environment, required positionals and color, and an action that reads
# files. Its decisions are pure defs that its laws state; act and the defs
# it calls above it hold the file IO.
# Expected output: ALL PROOFS CHECK.
# Run: bend examples/grep/app.bend --check-only

import Base
import ../../cli.bend as Cli

type Grep is Data:
  Grep{ignore_case: Bool, max: Maybe<&2, U32>, pattern: String,
    files: List<&2, String>}

def cli() -> Cli.Cmd:
  Cli.cmd("grep", String.concat(["Print lines that contain a pattern\n\n",
    "PATTERN is plain text, not a regular expression. Each FILE is read ",
    "whole, so it must be a regular file under 2 GiB. With more than one ",
    "FILE, each line starts with its file's name.\n\n",
    "Exits 0 if a line was printed, 1 if none was, and 2 if a file could ",
    "not be read."]), [
    Cli.version("1.0.0"),
    Cli.color(),
    Cli.arg("-i, --ignore-case", "Match ASCII letters in either case", []),
    Cli.arg("-m, --max-count <NUM>", "Stop after NUM matching lines per file",
      [Cli.as_u32(), Cli.env("GREP_MAX")]),
    Cli.arg("<PATTERN>", "Text to search for", []),
    Cli.arg("<FILE>...", "Files to search", [Cli.as_file()]),
    Cli.example("grep -i todo app.bend main.bend",
      "Find todo in any case in two files"),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(Grep):
  do Cli.Dec<Grep>:
    ignore_case : Bool <- Cli.flag(m, "ignore-case")
    max : Maybe<&2, U32> <- Cli.u32_opt(m, "max-count")
    pattern : String <- Cli.str(m, "pattern")
    files : List<&2, String> <- Cli.strs(m, "file")
    return Grep{ignore_case, max, pattern, files}

# ---- Search: pure ----

# s as it is compared: with ASCII letters in lower case when fold, as
# String.to_lower gives them; other letters keep their case.
def folded(fold: Bool, s: String) -> String:
  match fold:
    case True{}: String.to_lower(s)
    case False{}: s

# None is no limit; Some{n} allows n more lines.
def spent(left: Maybe<&2, U32>) -> Bool:
  match left:
    case None{}: False{}
    case Some{n}: U32.is_eq(n, 0)

def after(hit: Bool, left: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match hit left:
    case True{} Some{n}: Some{(n - 1 : U32)}
    case _ _: left

def put(hit: Bool, line: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}: line <> rest
    case False{}: rest

# The pieces that contain pat, which is already folded, up to left of them.
# stop ends the walk once left is spent. A last empty piece follows the
# text's final newline and is not a line.
def hits(pieces: List<&2, String>, stop: Bool, left: Maybe<&2, U32>,
    +fold: Bool, +pat: String) -> List<&2, String>:
  match pieces stop:
    case _ True{}: []
    case Nil{} False{}: []
    case Con{SNil{}, Nil{}} False{}: []
    case +line <> rest False{}:
      +hit = String.contains(folded(fold, line), pat)
      +next = after(hit, left)
      put(hit, line, hits(rest, spent(next), next, fold, pat))

# line with each match of pat painted bold red. low is line folded as pat
# is, n is pat's length, at least 1, and at says whether low starts with
# pat. Each step takes at least one char, so fuel above line's length
# suffices.
def mark(fuel: Nat, at: Bool, +line: String, low: String, +pat: String,
    +n: Nat) -> String:
  match fuel at:
    case 0n _: line
    case 1n+f True{}:
      +rest = String.drop(low, n)
      String.append(Cli.paint(True{}, [Cli.Bold{}, Cli.Red{}],
        String.take(line, n)),
        mark(f, String.starts_with(rest, pat), String.drop(line, n), rest,
          pat, n))
    case 1n+f False{}:
      match line low:
        case SCon{c, t} SCon{_, +lt}:
          SCon{c, mark(f, String.starts_with(lt, pat), t, lt, pat, n)}
        case _ _: line

# line as printed: its matches painted when paint.
def shown(paint: Bool, +line: String, fold: Bool, +pat: String) -> String:
  match paint:
    case False{}: line
    case True{}:
      +low = folded(fold, line)
      mark(1n+String.length(line), String.starts_with(low, pat), line, low,
        pat, String.length(pat))

def printed(lines: List<&2, String>, +paint: Bool, +fold: Bool, +pat: String,
    +prefix: String) -> String:
  match lines:
    case Nil{}: ""
    case line <> rest:
      String.concat([prefix, shown(paint, line, fold, pat), "\n",
        printed(rest, paint, fold, pat, prefix)])

# What grep prints for one file's text: each line that contains pat, up to
# max of them, after prefix. When on, matches are painted; an empty pat
# matches every line at no char, so nothing is.
def found(on: Bool, +fold: Bool, pat: String, +max: Maybe<&2, U32>,
    prefix: String, text: String) -> String:
  +p = folded(fold, pat)
  printed(hits(String.lines(text), spent(max), max, fold, p),
    Bool.and(on, Bool.not(String.is_empty(p))), fold, p, prefix)

# The start of each printed line: with several files, the file's name and
# a colon.
def prefix(+on: Bool, many: Bool, path: String) -> String:
  match many:
    case False{}: ""
    case True{}:
      String.append(Cli.paint(on, [Cli.Magenta{}], path),
        Cli.paint(on, [Cli.Cyan{}], ":"))

def several(files: List<&2, String>) -> Bool:
  match files:
    case Con{_, Con{_, _}}: True{}
    case _: False{}

# The exit status from whether a file failed and whether a line was printed.
def status(seen: Bool & Bool) -> U32:
  match seen:
    case (True{}, _): 2
    case (False{}, True{}): 0
    case (False{}, False{}): 1

# ---- Files: IO ----

def closed(got: File & Result<&1, &1, U32 & String, String>) ->
    IO(Result<&1, &1, U32 & String, String>):
  match got:
    case (file, r):
      do IO<Result<&1, &1, U32 & String, String>>:
        File.close(file)
        return r

# text if a read after it found the end, else EFBIG (27); report prints
# only the message.
def ended(more: File & Result<&1, &1, U32 & String, String>, text: String) ->
    IO(Result<&1, &1, U32 & String, String>):
  match more:
    case (file, Done{SNil{}}):
      closed((file, Done{text}))
    case (file, Done{_}):
      closed((file,
        Fail{(27, "not read whole: over 2 GiB, or changed while read")}))
    case (file, Fail{e}):
      closed((file, Fail{e}))

# One read returns at most 2 GiB, or less if the file grew, so a second
# read must find the end.
def whole(got: File & Result<&1, &1, U32 & String, String>) ->
    IO(Result<&1, &1, U32 & String, String>):
  match got:
    case (file, Fail{e}):
      closed((file, Fail{e}))
    case (file, Done{text}):
      do IO<Result<&1, &1, U32 & String, String>>:
        more : File & Result<&1, &1, U32 & String, String> <- File.read(file, 1)
        ended(more, text)

def read_sized(sized: File & Result<&1, &1, U32 & String, U32>) ->
    IO(Result<&1, &1, U32 & String, String>):
  match sized:
    case (file, Fail{e}):
      closed((file, Fail{e}))
    case (file, Done{n}):
      do IO<Result<&1, &1, U32 & String, String>>:
        got : File & Result<&1, &1, U32 & String, String> <- File.read(file, n)
        whole(got)

def read_opened(opened: Result<&1, &1, U32 & String, File>) ->
    IO(Result<&1, &1, U32 & String, String>):
  match opened:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, String>, Fail{e})
    case Done{file}:
      do IO<Result<&1, &1, U32 & String, String>>:
        sized : File & Result<&1, &1, U32 & String, U32> <- File.size(file)
        read_sized(sized)

# path's text, read in one piece at the size the file has when opened, so
# a file must be a regular file under 2 GiB that does not grow while read;
# a file that is not fails. A FIFO is out of scope: opening one waits for a
# writer. The file opens by path's argv bytes, so a name that is not UTF-8
# opens too.
def read_text(path: String) -> IO(Result<&1, &1, U32 & String, String>):
  do IO<Result<&1, &1, U32 & String, String>>:
    opened : Result<&1, &1, U32 & String, File> <-
      File.open_bytes(Cli.arg_bytes(path), "r")
    read_opened(opened)

# Prints a file's lines, or its error to stderr, and answers whether a file
# has failed and whether a line has been printed, so far.
def report(seen: Bool & Bool, r: Result<&1, &1, U32 & String, String>,
    +path: String, +many: Bool, +on: Bool, +fold: Bool, +pat: String,
    +max: Maybe<&2, U32>) -> IO(Bool & Bool):
  match seen r:
    case (_, saw) Fail{(_, msg)}:
      do IO<Bool & Bool>:
        IO.print_err(String.concat(["grep: ", path, ": ", msg]))
        return (True{}, saw)
    case (failed, saw) Done{text}:
      +out = found(on, fold, pat, max, prefix(on, many, path), text)
      do IO<Bool & Bool>:
        IO.write(out)
        return (failed, Bool.or(saw, Bool.not(String.is_empty(out))))

def search(files: List<&2, String>, seen: Bool & Bool, +many: Bool, +on: Bool,
    +fold: Bool, +pat: String, +max: Maybe<&2, U32>) -> IO(U32):
  match files:
    case Nil{}:
      IO.pure(U32, status(seen))
    case +path <> rest:
      do IO<U32>:
        r : Result<&1, &1, U32 & String, String> <- read_text(path)
        now : Bool & Bool <- report(seen, r, path, many, on, fold, pat, max)
        search(rest, now, many, on, fold, pat, max)

def act(+t: Cli.Term, g: Grep) -> IO(U32):
  match t g:
    case Cli.Term{out_color, _, _} Grep{ignore_case, max, pattern, +files}:
      search(files, (False{}, False{}), several(files), out_color,
        ignore_case, pattern, max)
