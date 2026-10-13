# Purpose: laws for the grep example: the definition check, the help pages,
# how argv and GREP_MAX decode or fail, and what a file's text prints.
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
    "  <PATTERN>              Text to search for\n",
    "  <FILE>...              Files to search\n",
    "\n",
    "Options:\n",
    "      --color <WHEN>     When to use color [default: auto] [possible values:\n",
    "                         auto, always, never]\n",
    "  -i, --ignore-case      Match ASCII letters in either case\n",
    "  -m, --max-count <NUM>  Stop after NUM matching lines per file [env: GREP_MAX]\n",
  ])

def examples() -> String:
  String.concat([
    "  -V, --version          Print version\n",
    "\n",
    "Examples:\n",
    "  Find todo in any case in two files:\n",
    "    $ grep -i todo app.bend main.bend\n",
  ])

# -h prints each text's first paragraph.
law help_short:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n), ["-h"])
    == Cli.Quit{0, String.concat([
      "Print lines that contain a pattern\n",
      "\n",
      options(),
      "  -h, --help             Print help (see more with '--help')\n",
      examples(),
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
      "Exits 0 if a line was printed, 1 if none was, and 2 if a file could not be read.\n",
      "\n",
      options(),
      "  -h, --help             Print help (see a summary with '-h')\n",
      examples(),
    ]), ""} : Cli.Step<App.Grep>}

law ignore_case:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["-i", "todo", "a.txt", "b.txt"])
    == Cli.Go{App.Grep{True{}, None{}, "todo", ["a.txt", "b.txt"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Grep>}

law env_max:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(),
    Cli.host_var(Cli.host(80n), "GREP_MAX", "3"), ["todo", "a.txt"])
    == Cli.Go{App.Grep{False{}, Some{3}, "todo", ["a.txt"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Grep>}

# A value in argv wins over the environment's.
law argv_max:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(),
    Cli.host_var(Cli.host(80n), "GREP_MAX", "3"), ["-m", "1", "todo", "a.txt"])
    == Cli.Go{App.Grep{False{}, Some{1}, "todo", ["a.txt"]},
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

# --color=always turns color on for both streams, even off a terminal.
law color_always:
  {Cli.eval(~App.Grep, ~App.decode, App.cli(), Cli.host(80n),
    ["--color=always", "todo", "a.txt"])
    == Cli.Go{App.Grep{False{}, None{}, "todo", ["a.txt"]},
      Cli.Term{True{}, True{}, 80n}} : Cli.Step<App.Grep>}

def text() -> String:
  "TODO a\nb\ntodo c\nToDo d\n"

law found_exact:
  {App.found(False{}, False{}, "todo", None{}, "", text()) == "todo c\n"
    : String}

# -i matches in any case; -m 2 stops after the second line printed.
law found_fold_max:
  {App.found(False{}, True{}, "todo", Some{2}, "", text())
    == "TODO a\ntodo c\n" : String}

# -m 0 prints nothing, though lines match.
law found_none:
  {App.found(False{}, False{}, "todo", Some{0}, "", text()) == "" : String}

# -i folds ASCII letters only, as Base's String.to_lower does.
law found_ascii_fold:
  {App.found(False{}, True{}, "\u{E9}", None{}, "", "\u{C9}\n\u{E9}\n")
    == "\u{E9}\n" : String}

# An empty pattern matches every line; the final newline ends the last line
# and starts none.
law found_every_line:
  {App.found(False{}, False{}, "", None{}, "", "a\n\nb\n") == "a\n\nb\n"
    : String}

# With color, the file name is magenta, the colon cyan and each match bold
# red, in the line's own case.
law found_paint:
  {App.found(True{}, True{}, "do", None{}, App.prefix(True{}, True{}, "f"),
    "To do: Do\n")
    == "\u{1B}[35mf\u{1B}[0m\u{1B}[36m:\u{1B}[0mTo \u{1B}[1;31mdo\u{1B}[0m: \u{1B}[1;31mDo\u{1B}[0m\n"
    : String}

# 2 after a file failed, whatever was printed; else 0 if a line was printed.
law status:
  for printed: Bool
  {App.status((True{}, printed)) == 2 : U32} &
  {App.status((False{}, True{})) == 0 : U32} &
  {App.status((False{}, False{})) == 1 : U32}
