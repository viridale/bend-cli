# Purpose: the grep example app: flags, an option read from argv or the
# environment, a negatable flag, a conflict and an exclusive group, help
# headings, required positionals and color, and an action that reads
# files. Its decisions are pure defs that its laws state; act and the defs
# it calls above it hold the file IO.
# Expected output: ALL PROOFS CHECK.
# Run: bend examples/grep/app.bend --check-only

import Base
import ../../cli.bend as Cli

# What grep prints for each file: its selected lines (-o: their matches),
# a count of them (-c), its name if it has one (-l), or nothing (-q).
type Mode is Data:
  Lines{}
  Count{}
  Names{}
  Quiet{}

# How grep searches and prints each file, its fields in --help's order.
type Scan is Data:
  Scan{ignore_case: Bool, invert: Bool, max: Maybe<&2, U32>, number: Bool,
    names: Bool, only: Bool, mode: Mode, pattern: String}

type Grep is Data:
  Grep{scan: Scan, files: List<&2, String>}

def cli() -> Cli.Cmd:
  Cli.cmd("grep", String.concat(["Print lines that contain a pattern\n\n",
    "PATTERN is plain text, not a regular expression. Each FILE is read ",
    "whole, so it must be a regular file under 2 GiB. With more than one ",
    "FILE, each line starts with its file's name."]), [
    Cli.version("1.0.0"),
    Cli.color(),
    Cli.arg("-i, --ignore-case", "Match ASCII letters in either case",
      [Cli.heading("Matching")]),
    Cli.arg("-v, --invert-match", "Select the lines that do not match",
      [Cli.heading("Matching")]),
    Cli.arg("-m, --max-count <NUM>", "Select at most NUM lines per file",
      [Cli.as_u32(), Cli.env("GREP_MAX"), Cli.heading("Matching")]),
    Cli.arg("-n, --line-number", "Start each line with its line number",
      [Cli.heading("Output")]),
    Cli.arg("--[no-]filename", "Start each line with its file's name",
      [Cli.heading("Output")]),
    Cli.arg("-o, --only-matching", "Print each match on a line of its own",
      [Cli.conflicts("invert-match"), Cli.heading("Output")]),
    Cli.arg("-c, --count", "Print only each file's count of selected lines",
      [Cli.group("mode"), Cli.heading("Output")]),
    Cli.arg("-l, --files-with-matches",
      "Print only the names of files with a selected line",
      [Cli.group("mode"), Cli.heading("Output")]),
    Cli.arg("-q, --quiet", "Print nothing, and stop at the first selected line",
      [Cli.group("mode"), Cli.heading("Output")]),
    Cli.exclusive("mode"),
    Cli.arg("<PATTERN>", "Text to search for", []),
    Cli.arg("<FILE>...", "Files to search", [Cli.as_file()]),
    Cli.example("grep -i todo app.bend main.bend",
      "Find todo in any case in two files"),
    Cli.example("grep -cv todo app.bend main.bend",
      "Count the lines without todo in each file"),
    Cli.after(String.concat(["Exits 0 if a line was selected, 1 if none was, ",
      "and 2 if a file could not be read, unless -q selected a line."])),
  ])

def several(files: List<&2, String>) -> Bool:
  match files:
    case Con{_, Con{_, _}}: True{}
    case _: False{}

# Whether each line starts with its file's name: as --[no-]filename says,
# else with more than one FILE.
def names_of(src: Cli.Src, on: Bool, files: List<&2, String>) -> Bool:
  match src:
    case Cli.Argv{}: on
    case Cli.Env{}: on
    case Cli.Default{}: on
    case Cli.Absent{}: several(files)

# The exclusive group lets at most one of -c, -l and -q through.
def mode_of(count: Bool, list: Bool, quiet: Bool) -> Mode:
  match count list quiet:
    case True{} _ _: Count{}
    case False{} True{} _: Names{}
    case False{} False{} True{}: Quiet{}
    case False{} False{} False{}: Lines{}

def decode(+m: Cli.Matches) -> Cli.Dec(Grep):
  do Cli.Dec<Grep>:
    ignore_case : Bool <- Cli.flag(m, "ignore-case")
    invert : Bool <- Cli.flag(m, "invert-match")
    max : Maybe<&2, U32> <- Cli.u32_opt(m, "max-count")
    number : Bool <- Cli.flag(m, "line-number")
    named : Bool <- Cli.flag(m, "filename")
    src : Cli.Src <- Cli.source(m, "filename")
    only : Bool <- Cli.flag(m, "only-matching")
    count : Bool <- Cli.flag(m, "count")
    list : Bool <- Cli.flag(m, "files-with-matches")
    quiet : Bool <- Cli.flag(m, "quiet")
    pattern : String <- Cli.str(m, "pattern")
    +files : List<&2, String> <- Cli.strs(m, "file")
    return Grep{Scan{ignore_case, invert, max, number,
      names_of(src, named, files), only, mode_of(count, list, quiet),
      pattern}, files}

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

# A line is selected when it has the pattern, or under -v when it has not.
def selects(invert: Bool, has: Bool) -> Bool:
  match invert:
    case True{}: Bool.not(has)
    case False{}: has

# A selected line and its number among the file's lines, from 1.
type Line is Data:
  Line{n: U32, text: String}

def put(hit: Bool, line: Line, rest: List<&2, Line>) -> List<&2, Line>:
  match hit:
    case True{}: line <> rest
    case False{}: rest

# The selected pieces, numbered from n, up to left of them; pat is already
# folded. stop ends the walk once left is spent. A last empty piece follows
# the text's final newline and is not a line.
def hits(pieces: List<&2, String>, stop: Bool, +n: U32,
    left: Maybe<&2, U32>, +fold: Bool, +invert: Bool, +pat: String) ->
    List<&2, Line>:
  match pieces stop:
    case _ True{}: []
    case Nil{} False{}: []
    case Con{SNil{}, Nil{}} False{}: []
    case +line <> rest False{}:
      +hit = selects(invert, String.contains(folded(fold, line), pat))
      +next = after(hit, left)
      put(hit, Line{n, line},
        hits(rest, spent(next), (n + 1 : U32), next, fold, invert, pat))

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

# The matches of pat in line, in line's case, as mark finds them: each
# taken whole, and the next sought after it.
def parts(fuel: Nat, at: Bool, +line: String, low: String, +pat: String,
    +n: Nat) -> List<&2, String>:
  match fuel at:
    case 0n _: []
    case 1n+f True{}:
      +rest = String.drop(low, n)
      String.take(line, n) <> parts(f, String.starts_with(rest, pat),
        String.drop(line, n), rest, pat, n)
    case 1n+f False{}:
      match line low:
        case SCon{_, t} SCon{_, +lt}:
          parts(f, String.starts_with(lt, pat), t, lt, pat, n)
        case _ _: []

# The matches of pat, folded as low is, in line; none when pat is empty,
# which matches at no char.
def matches(empty: Bool, +line: String, +low: String, +pat: String) ->
    List<&2, String>:
  match empty:
    case True{}: []
    case False{}:
      parts(1n+String.length(line), String.starts_with(low, pat), line, low,
        pat, String.length(pat))

# The start of each printed line: the file's name and a colon when names,
# magenta and cyan with color.
def name_lead(on: Bool, names: Bool, path: String) -> String:
  match names:
    case False{}: ""
    case True{}:
      Cli.emit(on, [Cli.Segment{path, [Cli.Magenta{}]},
        Cli.Segment{":", [Cli.Cyan{}]}])

# After it, the line's number and a colon under -n, green and cyan with
# color.
def number_lead(on: Bool, number: Bool, n: U32) -> String:
  match number:
    case False{}: ""
    case True{}:
      Cli.emit(on, [Cli.Segment{U32.show(n), [Cli.Green{}]},
        Cli.Segment{":", [Cli.Cyan{}]}])

def part_lines(parts: List<&2, String>, +lead: String, +paint: Bool) ->
    String:
  match parts:
    case Nil{}: ""
    case part <> rest:
      String.concat([lead, Cli.paint(paint, [Cli.Bold{}, Cli.Red{}], part),
        "\n", part_lines(rest, lead, paint)])

# A selected line as printed after lead: whole, with its matches painted
# when paint, or under -o each match on a line of its own.
def entry(only: Bool, lead: String, +line: String, paint: Bool, fold: Bool,
    +pat: String) -> String:
  match only:
    case False{}: String.concat([lead, shown(paint, line, fold, pat), "\n"])
    case True{}:
      +low = folded(fold, line)
      part_lines(matches(String.is_empty(pat), line, low, pat), lead, paint)

def printed(lines: List<&2, Line>, +head: String, +on: Bool, +number: Bool,
    +only: Bool, +paint: Bool, +fold: Bool, +pat: String) -> String:
  match lines:
    case Nil{}: ""
    case Line{n, line} <> rest:
      String.append(
        entry(only, String.append(head, number_lead(on, number, n)), line,
          paint, fold, pat),
        printed(rest, head, on, number, only, paint, fold, pat))

def listed(lines: List<&2, Line>) -> Bool:
  match lines:
    case Nil{}: False{}
    case _ <> _: True{}

def tally(lines: List<&2, Line>, k: U32) -> U32:
  match lines:
    case Nil{}: k
    case _ <> rest: tally(rest, (k + 1 : U32))

def name_line(hit: Bool, on: Bool, path: String) -> String:
  match hit:
    case True{}: String.append(Cli.paint(on, [Cli.Magenta{}], path), "\n")
    case False{}: ""

# What grep prints for one file, and whether it selected a line.
type Found is Data:
  Found{selected: Bool, text: String}

# A file's selected lines as each mode prints them. An empty pat matches
# every line at no char, so no match is painted.
def shows(mode: Mode, +lines: List<&2, Line>, +on: Bool, path: String,
    names: Bool, number: Bool, only: Bool, fold: Bool, +pat: String) ->
    Found:
  match mode:
    case Lines{}:
      Found{listed(lines),
        printed(lines, name_lead(on, names, path), on, number, only,
          Bool.and(on, Bool.not(String.is_empty(pat))), fold, pat)}
    case Count{}:
      +k = tally(lines, 0)
      Found{U32.is_lt(0, k),
        String.concat([name_lead(on, names, path), U32.show(k), "\n"])}
    case Names{}:
      +hit = listed(lines)
      Found{hit, name_line(hit, on, path)}
    case Quiet{}:
      Found{listed(lines), ""}

# What grep prints for one file's text when on says stdout has color.
def found(scan: Scan, on: Bool, path: String, text: String) -> Found:
  match scan:
    case Scan{+fold, invert, +max, number, names, only, mode, pattern}:
      +p = folded(fold, pattern)
      shows(mode, hits(String.lines(text), spent(max), 1, max, fold, invert,
        p), on, path, names, number, only, fold, p)

def loud_status(seen: Bool & Bool) -> U32:
  match seen:
    case (True{}, _): 2
    case (False{}, True{}): 0
    case (False{}, False{}): 1

def quiet_status(seen: Bool & Bool) -> U32:
  match seen:
    case (_, True{}): 0
    case (True{}, False{}): 2
    case (False{}, False{}): 1

# The exit status from -q, whether a file failed and whether a line was
# selected.
def status(quiet: Bool, seen: Bool & Bool) -> U32:
  match quiet:
    case True{}: quiet_status(seen)
    case False{}: loud_status(seen)

def selected_of(seen: Bool & Bool) -> Bool:
  match seen:
    case (_, selected): selected

# Whether grep reads no more files: -q needs only one selected line.
def stops(quiet: Bool, seen: Bool & Bool) -> Bool:
  match quiet:
    case True{}: selected_of(seen)
    case False{}: False{}

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

# After each file: whether grep reads no more files, whether a file has
# failed, and whether a line has been selected, so far.
type Seen is Data:
  Seen{stop: Bool, failed: Bool, selected: Bool}

def seen(+quiet: Bool, +failed: Bool, +selected: Bool) -> Seen:
  Seen{stops(quiet, (failed, selected)), failed, selected}

def written(f: Found, quiet: Bool, failed: Bool, saw: Bool) -> IO(Seen):
  match f:
    case Found{selected, text}:
      do IO<Seen>:
        IO.write(text)
        return seen(quiet, failed, Bool.or(saw, selected))

# Prints a file's output, or its error to stderr.
def report(r: Result<&1, &1, U32 & String, String>, failed: Bool, saw: Bool,
    path: String, quiet: Bool, on: Bool, scan: Scan) -> IO(Seen):
  match r:
    case Fail{(_, msg)}:
      do IO<Seen>:
        IO.print_err(String.concat(["grep: ", path, ": ", msg]))
        return seen(quiet, True{}, saw)
    case Done{text}:
      written(found(scan, on, path, text), quiet, failed, saw)

def search(files: List<&2, String>, now: Seen, +quiet: Bool, +on: Bool,
    +scan: Scan) -> IO(U32):
  match files now:
    case _ Seen{True{}, failed, selected}:
      IO.pure(U32, status(quiet, (failed, selected)))
    case Nil{} Seen{False{}, failed, selected}:
      IO.pure(U32, status(quiet, (failed, selected)))
    case +path <> rest Seen{False{}, failed, selected}:
      do IO<U32>:
        r : Result<&1, &1, U32 & String, String> <- read_text(path)
        next : Seen <- report(r, failed, selected, path, quiet, on, scan)
        search(rest, next, quiet, on, scan)

def quiet_mode(mode: Mode) -> Bool:
  match mode:
    case Lines{}: False{}
    case Count{}: False{}
    case Names{}: False{}
    case Quiet{}: True{}

def quiet_of(scan: Scan) -> Bool:
  match scan:
    case Scan{fold, invert, max, number, names, only, mode, pattern}:
      quiet_mode(mode)

def act(+t: Cli.Term, g: Grep) -> IO(U32):
  match t g:
    case Cli.Term{out_color, _, _} Grep{+scan, files}:
      search(files, Seen{False{}, False{}, False{}}, quiet_of(scan),
        out_color, scan)
