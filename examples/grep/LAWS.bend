# Purpose: laws for the grep example: the definition check, the help pages,
# how argv and GREP_MAX decode or fail, what a file's text prints in each
# mode, and the exit status.
# Expected output: ALL PROOFS CHECK.
# Run: bend examples/grep/PROOF.bend --verdict

import Base
import ./app.bend as App
import ../../cli.bend as Cli

law cli_ok:
  {Cli.check(~App.Grep, ~App.decode, App.cli()) == []
    : List<&2, Cli.Problem>}

def options() -> String:
  String.concat([
    "Usage: grep [OPTIONS] <PATTERN> <FILE>...\n",
    "\n",
    "Arguments:\n",
    "  <PATTERN>                 Text to search for\n",
    "  <FILE>...                 Files to search\n",
    "\n",
    "Options:\n",
    "      --color <WHEN>        When to use color [default: auto] [possible values:\n",
    "                            auto, always, never]\n",
  ])

def sections() -> String:
  String.concat([
    "  -V, --version             Print version\n",
    "\n",
    "Matching:\n",
    "  -i, --ignore-case         Match ASCII letters in either case\n",
    "  -v, --invert-match        Select the lines that do not match\n",
    "  -m, --max-count <NUM>     Select at most NUM lines per file [env: GREP_MAX]\n",
    "\n",
    "Output:\n",
    "  -n, --line-number         Start each line with its line number\n",
    "      --[no-]filename       Start each line with its file's name\n",
    "  -o, --only-matching       Print each match on a line of its own\n",
    "  -c, --count               Print only each file's count of selected lines\n",
    "  -l, --files-with-matches  Print only the names of files with a selected line\n",
    "  -q, --quiet               Print nothing, and stop at the first selected line\n",
    "\n",
    "Examples:\n",
    "  Find todo in any case in two files:\n",
    "    $ grep -i todo app.bend main.bend\n",
    "  Count the lines without todo in each file:\n",
    "    $ grep -cv todo app.bend main.bend\n",
    "\n",
    "Exits 0 if a line was selected, 1 if none was, and 2 if a file could not be\n",
    "read, unless -q selected a line.\n",
  ])

# -h prints each text's first paragraph; each heading's options follow
# Options, in a section of their own.
law help_short:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n), ["-h"])
    == Cli.Quit{0, String.concat([
      "Print lines that contain a pattern\n",
      "\n",
      options(),
      "  -h, --help                Print help (see more with '--help')\n",
      sections(),
    ]), ""} : Cli.Step<App.Grep>}

# --help prints every paragraph.
law help_long:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n), ["--help"])
    == Cli.Quit{0, String.concat([
      "Print lines that contain a pattern\n",
      "\n",
      "PATTERN is plain text, not a regular expression. Each FILE is read whole, so it\n",
      "must be a regular file under 2 GiB. With more than one FILE, each line starts\n",
      "with its file's name.\n",
      "\n",
      options(),
      "  -h, --help                Print help (see a summary with '-h')\n",
      sections(),
    ]), ""} : Cli.Step<App.Grep>}

# A Scan's fields, in --help's order: -i, -v, -m, -n, whether each line
# starts with its file's name, -o, the mode, and the pattern.
law ignore_case:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-i", "todo", "a.txt", "b.txt"])
    == Cli.Go{App.Grep{App.Scan{True{}, False{}, None{}, False{}, True{},
      False{}, App.Lines{}, "todo"}, ["a.txt", "b.txt"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Grep>}

law env_max:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(),
    Cli.host_var(Cli.host(80n), "GREP_MAX", "3"), ["todo", "a.txt"])
    == Cli.Go{App.Grep{App.Scan{False{}, False{}, Some{3}, False{}, False{},
      False{}, App.Lines{}, "todo"}, ["a.txt"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Grep>}

# A value in argv wins over the environment's.
law argv_max:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(),
    Cli.host_var(Cli.host(80n), "GREP_MAX", "3"), ["-m", "1", "todo", "a.txt"])
    == Cli.Go{App.Grep{App.Scan{False{}, False{}, Some{1}, False{}, False{},
      False{}, App.Lines{}, "todo"}, ["a.txt"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Grep>}

# Each flag sets its own field; --filename names the file of one FILE and
# --no-filename neither of two; -c, -l and -q each set their mode.
law decode_flags:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-v", "-n", "--filename", "-c", "x", "f"])
    == Cli.Go{App.Grep{App.Scan{False{}, True{}, None{}, True{}, True{},
      False{}, App.Count{}, "x"}, ["f"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Grep>} &
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-i", "-o", "--no-filename", "-q", "-m", "5", "x", "f", "g"])
    == Cli.Go{App.Grep{App.Scan{True{}, False{}, Some{5}, False{}, False{},
      True{}, App.Quiet{}, "x"}, ["f", "g"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Grep>} &
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-l", "x", "f"])
    == Cli.Go{App.Grep{App.Scan{False{}, False{}, None{}, False{}, False{},
      False{}, App.Names{}, "x"}, ["f"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Grep>}

law bad_max:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-m", "lots", "todo", "a.txt"])
    == Cli.Quit{2, "", String.concat([
      "error: invalid value 'lots' for '--max-count <NUM>': expected a whole number from 0 to 4294967295\n",
      "\n",
      "Usage: grep [OPTIONS] <PATTERN> <FILE>...\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Grep>}

law no_file:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n), ["todo"])
    == Cli.Quit{2, "", String.concat([
      "error: the following required arguments were not provided:\n",
      "  <FILE>...\n",
      "\n",
      "Usage: grep [OPTIONS] <PATTERN> <FILE>...\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Grep>}

# A usage error's message, then the usage line.
def refused(message: String) -> String:
  String.concat([
    "error: ", message, "\n",
    "\n",
    "Usage: grep [OPTIONS] <PATTERN> <FILE>...\n",
    "\n",
    "For more information, try '--help'.\n",
  ])

# -c, -l and -q each say what to print, so any two of them are an error.
law one_mode:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-c", "-l", "x", "f"])
    == Cli.Quit{2, "", refused(
      "the argument '--files-with-matches' cannot be used with '--count'")}
    : Cli.Step<App.Grep>} &
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-lq", "x", "f"])
    == Cli.Quit{2, "", refused(
      "the argument '--quiet' cannot be used with '--files-with-matches'")}
    : Cli.Step<App.Grep>}

# A line -v selects has no match for -o to print, so the two are an error.
law only_invert:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-o", "-v", "x", "f"])
    == Cli.Quit{2, "", refused(
      "the argument '--invert-match' cannot be used with '--only-matching'")}
    : Cli.Step<App.Grep>}

# --color=always turns color on for both streams, even off a terminal.
law color_always:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["--color=always", "todo", "a.txt"])
    == Cli.Go{App.Grep{App.Scan{False{}, False{}, None{}, False{}, False{},
      False{}, App.Lines{}, "todo"}, ["a.txt"]},
      Cli.Term{True{}, True{}, 80n}} : Cli.Step<App.Grep>}

def found_go(g: App.Grep, t: Cli.Term, path: String, text: String) ->
    App.Found:
  match g t:
    case App.Grep{scan, files} Cli.Term{on, err, width}:
      App.found(scan, on, path, text)

def found_at(s: Cli.Step<App.Grep>, path: String, text: String) ->
    Maybe<&2, App.Found>:
  match s:
    case Cli.Go{g, t}: Some{found_go(g, t, path, text)}
    case Cli.Quit{code, out, err}: None{}

# What grep prints for the file at path, whose text is text, and whether
# it selected a line there, when argv decodes off a terminal: stdout has
# color only with --color=always.
def grep(argv: List<&2, String>, path: String, text: String) ->
    Maybe<&2, App.Found>:
  found_at(Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n), argv),
    path, text)

def text() -> String:
  "TODO a\nb\ntodo c\nToDo d\n"

law found_exact:
  {grep(["todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "todo c\n"}} : Maybe<&2, App.Found>}

# -i matches in any case; -m 2 stops after the second line printed.
law found_fold_max:
  {grep(["-i", "-m", "2", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "TODO a\ntodo c\n"}} : Maybe<&2, App.Found>}

# -m 0 prints nothing, though lines match.
law found_none:
  {grep(["-m", "0", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{False{}, ""}} : Maybe<&2, App.Found>}

# -i folds ASCII letters only, as Base's String.to_lower does.
law found_ascii_fold:
  {grep(["-i", "\u{E9}", "a.txt"], "a.txt", "\u{C9}\n\u{E9}\n")
    == Some{App.Found{True{}, "\u{E9}\n"}} : Maybe<&2, App.Found>}

# An empty pattern matches every line; the final newline ends the last line
# and starts none.
law found_every_line:
  {grep(["", "a.txt"], "a.txt", "a\n\nb\n")
    == Some{App.Found{True{}, "a\n\nb\n"}} : Maybe<&2, App.Found>}

# With color, the file name is magenta, the colon cyan and each match bold
# red, in the line's own case.
law found_paint:
  {grep(["--color=always", "-i", "do", "f", "g"], "f", "To do: Do\n")
    == Some{App.Found{True{},
      "\u{1B}[35mf\u{1B}[0m\u{1B}[36m:\u{1B}[0mTo \u{1B}[1;31mdo\u{1B}[0m: \u{1B}[1;31mDo\u{1B}[0m\n"}}
    : Maybe<&2, App.Found>}

# --filename names the file of one FILE, --no-filename neither of two, and
# the later of the two wins.
law found_filename:
  {grep(["--filename", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "a.txt:todo c\n"}} : Maybe<&2, App.Found>} &
  {grep(["--no-filename", "todo", "a.txt", "b.txt"], "a.txt", text())
    == Some{App.Found{True{}, "todo c\n"}} : Maybe<&2, App.Found>} &
  {grep(["--no-filename", "--filename", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "a.txt:todo c\n"}} : Maybe<&2, App.Found>}

# -v selects the lines without a match, in -i's case too, and -m counts
# the lines it selects; an empty pattern is in every line, so -v selects
# none.
law found_invert:
  {grep(["-v", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "TODO a\nb\nToDo d\n"}}
    : Maybe<&2, App.Found>} &
  {grep(["-vi", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "b\n"}} : Maybe<&2, App.Found>} &
  {grep(["-v", "-m", "1", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "TODO a\n"}} : Maybe<&2, App.Found>} &
  {grep(["-v", "", "a.txt"], "a.txt", "a\n\nb\n")
    == Some{App.Found{False{}, ""}} : Maybe<&2, App.Found>}

# -n starts each line with its number among all the file's lines, after
# the file's name; with color the number is green and each colon cyan.
law found_numbers:
  {grep(["-n", "-i", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "1:TODO a\n3:todo c\n4:ToDo d\n"}}
    : Maybe<&2, App.Found>} &
  {grep(["-n", "todo", "a.txt", "b.txt"], "a.txt", text())
    == Some{App.Found{True{}, "a.txt:3:todo c\n"}} : Maybe<&2, App.Found>} &
  {grep(["--color=always", "-n", "do", "f", "g"], "f", "x\ndo\n")
    == Some{App.Found{True{},
      "\u{1B}[35mf\u{1B}[0m\u{1B}[36m:\u{1B}[0m\u{1B}[32m2\u{1B}[0m\u{1B}[36m:\u{1B}[0m\u{1B}[1;31mdo\u{1B}[0m\n"}}
    : Maybe<&2, App.Found>}

# -o prints each match in a selected line on a line of its own, in the
# line's case and after the line's name and number; matches do not
# overlap, and an empty pattern selects every line but prints no match.
law found_only:
  {grep(["-o", "-n", "-i", "do", "f"], "f", "To do: Do\nno\n")
    == Some{App.Found{True{}, "1:do\n1:Do\n"}} : Maybe<&2, App.Found>} &
  {grep(["-o", "aa", "f"], "f", "aaaa aaa\n")
    == Some{App.Found{True{}, "aa\naa\naa\n"}} : Maybe<&2, App.Found>} &
  {grep(["-o", "", "f"], "f", "a\n")
    == Some{App.Found{True{}, ""}} : Maybe<&2, App.Found>} &
  {grep(["--color=always", "-o", "do", "f", "g"], "f", "do do\n")
    == Some{App.Found{True{},
      "\u{1B}[35mf\u{1B}[0m\u{1B}[36m:\u{1B}[0m\u{1B}[1;31mdo\u{1B}[0m\n\u{1B}[35mf\u{1B}[0m\u{1B}[36m:\u{1B}[0m\u{1B}[1;31mdo\u{1B}[0m\n"}}
    : Maybe<&2, App.Found>}

# -c prints a file's count of selected lines, after its name and a colon,
# in place of the lines: it counts -v's lines and at most -m of them, -n
# and -o change nothing, and the count has no color. A count of 0 prints
# but selects no line.
law found_count:
  {grep(["-c", "-i", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "3\n"}} : Maybe<&2, App.Found>} &
  {grep(["-c", "-v", "todo", "a.txt", "b.txt"], "a.txt", text())
    == Some{App.Found{True{}, "a.txt:3\n"}} : Maybe<&2, App.Found>} &
  {grep(["-c", "-i", "-m", "2", "-n", "-o", "todo", "a.txt"], "a.txt",
    text())
    == Some{App.Found{True{}, "2\n"}} : Maybe<&2, App.Found>} &
  {grep(["-c", "nope", "a.txt"], "a.txt", text())
    == Some{App.Found{False{}, "0\n"}} : Maybe<&2, App.Found>} &
  {grep(["--color=always", "-c", "todo", "f", "g"], "f", text())
    == Some{App.Found{True{}, "\u{1B}[35mf\u{1B}[0m\u{1B}[36m:\u{1B}[0m1\n"}}
    : Maybe<&2, App.Found>}

# -l prints the name of a file with a selected line, magenta with color,
# whatever --no-filename says, and nothing for a file with none.
law found_names:
  {grep(["-l", "todo", "a.txt"], "a.txt", text())
    == Some{App.Found{True{}, "a.txt\n"}} : Maybe<&2, App.Found>} &
  {grep(["-l", "--no-filename", "-v", "todo", "a.txt", "b.txt"], "a.txt",
    text())
    == Some{App.Found{True{}, "a.txt\n"}} : Maybe<&2, App.Found>} &
  {grep(["-l", "nope", "a.txt"], "a.txt", text())
    == Some{App.Found{False{}, ""}} : Maybe<&2, App.Found>} &
  {grep(["--color=always", "-l", "-m", "0", "todo", "f"], "f", text())
    == Some{App.Found{False{}, ""}} : Maybe<&2, App.Found>} &
  {grep(["--color=always", "-l", "todo", "f"], "f", text())
    == Some{App.Found{True{}, "\u{1B}[35mf\u{1B}[0m\n"}}
    : Maybe<&2, App.Found>}

# -q prints nothing, whether or not it selects a line.
law found_quiet:
  {grep(["-q", "-n", "todo", "a.txt", "b.txt"], "a.txt", text())
    == Some{App.Found{True{}, ""}} : Maybe<&2, App.Found>} &
  {grep(["-q", "nope", "a.txt"], "a.txt", text())
    == Some{App.Found{False{}, ""}} : Maybe<&2, App.Found>}

# The exit status from -q and from whether a file failed and whether a line
# was selected: 2 after a file failed, unless -q selected a line; else 0 if
# a line was selected, and 1 if none was.
law status:
  for selected: Bool
  for quiet: Bool
  {App.status(False{}, (True{}, selected)) == 2 : U32} &
  {App.status(quiet, (True{}, False{})) == 2 : U32} &
  {App.status(True{}, (True{}, True{})) == 0 : U32} &
  {App.status(quiet, (False{}, True{})) == 0 : U32} &
  {App.status(quiet, (False{}, False{})) == 1 : U32}

# Whether grep reads no more files: with -q, once a line was selected,
# whether or not a file failed; without it, never.
law stops:
  for failed: Bool
  for selected: Bool
  {App.stops(True{}, (failed, True{})) == True{} : Bool} &
  {App.stops(True{}, (failed, False{})) == False{} : Bool} &
  {App.stops(False{}, (failed, selected)) == False{} : Bool}
