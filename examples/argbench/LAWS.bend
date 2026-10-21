# Purpose: laws for the argbench example: the definition check, the help
# pages, how argv decodes or fails, and the line the action prints. The
# decode laws cover the forms tools/peerbench.sh feeds every peer; each
# error law pins a message the benchmark's error case prints.
# Expected output: ALL PROOFS CHECK.
# Run: bend examples/argbench/PROOF.bend --verdict

import Base
import ./app.bend as App
import ../../cli.bend as Cli

law cli_ok:
  {Cli.check(~App.Job, ~App.decode, App.cli()) == []
    : List<&2, Cli.Problem>}

def root() -> String:
  String.concat([
    "Print the line an argv decodes to\n",
    "\n",
    "Usage: argbench <COMMAND>\n",
    "\n",
    "Commands:\n",
    "  build       Build inputs\n",
    "  check       Check inputs\n",
    "  help        Print this message or the help of the given subcommand(s)\n",
    "\n",
    "Options:\n",
    "  -h, --help  Print help\n",
  ])

# Each text has one paragraph, so -h and --help print the same page.
law help:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n), ["-h"])
    == Cli.Quit{0, root(), ""} : Cli.Step<App.Job>} &
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n), ["--help"])
    == Cli.Quit{0, root(), ""} : Cli.Step<App.Job>}

# With no command, the root's help goes to stderr as an error.
law no_command:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n), [])
    == Cli.Quit{2, "", root()} : Cli.Step<App.Job>}

def build_page() -> String:
  String.concat([
    "Build inputs\n",
    "\n",
    "Usage: argbench build [OPTIONS] <INPUT>...\n",
    "\n",
    "Arguments:\n",
    "  <INPUT>...              Files to build\n",
    "\n",
    "Options:\n",
    "  -v, --verbose...        More output; repeat for more\n",
    "  -q, --quiet             Less output\n",
    "  -o, --output <FILE>     Write the result to FILE [default: out]\n",
    "  -I, --include <DIR>...  Search DIR for inputs\n",
    "  -j, --jobs <N>          Run N jobs at once [default: 1]\n",
    "  -f, --format <FMT>      Output format [default: text] [possible values: text,\n",
    "                          json, csv]\n",
    "  -h, --help              Print help\n",
  ])

law build_help:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "-h"])
    == Cli.Quit{0, build_page(), ""} : Cli.Step<App.Job>} &
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "--help"])
    == Cli.Quit{0, build_page(), ""} : Cli.Step<App.Job>}

# The benchmark's small argv: each option in its separate form.
law typical:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "-vv", "-o", "out.bin", "-I", "src", "-I", "lib", "-j", "4",
      "-f", "json", "a.c", "b.c"])
    == Cli.Go{App.Build{2n, False{}, "out.bin", ["src", "lib"], 4,
      App.Json{}, ["a.c", "b.c"]}, Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Job>}

# Clustered flags count each letter, and a value may be attached to its
# short or long name.
law forms:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "-vvq", "-oout.bin", "--include=src", "-Ilib", "--jobs=4",
      "-fjson", "a.c"])
    == Cli.Go{App.Build{2n, True{}, "out.bin", ["src", "lib"], 4,
      App.Json{}, ["a.c"]}, Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Job>}

law defaults:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "a.c"])
    == Cli.Go{App.Build{0n, False{}, "out", [], 1, App.Plain{}, ["a.c"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Job>}

# A repeated single-value option takes its last value; a repeatable one
# keeps every value in argv order.
law repeats:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "-o", "a", "-I", "y", "-o", "b", "-I", "x", "-j", "2", "-j",
      "3", "in"])
    == Cli.Go{App.Build{0n, False{}, "b", ["y", "x"], 3, App.Plain{},
      ["in"]}, Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Job>}

# After --, an argument that looks like an option is an input.
law dash:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "--", "-x"])
    == Cli.Go{App.Build{0n, False{}, "out", [], 1, App.Plain{}, ["-x"]},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Job>}

# A repeated flag is still one flag.
law check:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["check", "-s", "-s", "a", "b"])
    == Cli.Go{App.Check{True{}, ["a", "b"]}, Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Job>}

# The benchmark's error argv: a misspelt option and the one it resembles.
law typo:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "--ouput", "x", "a.c"])
    == Cli.Quit{2, "", String.concat([
      "error: unexpected argument '--ouput' found\n",
      "\n",
      "  tip: a similar argument exists: '--output'\n",
      "  tip: to pass '--ouput' as a value, use '-- --ouput'\n",
      "\n",
      "Usage: argbench build [OPTIONS] <INPUT>...\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Job>}

# --jobs takes the largest U32 and rejects one more.
law jobs_limit:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "-j", "4294967295", "a"])
    == Cli.Go{App.Build{0n, False{}, "out", [], 4294967295, App.Plain{},
      ["a"]}, Cli.Term{False{}, False{}, 80n}} : Cli.Step<App.Job>} &
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "-j", "4294967296", "a"])
    == Cli.Quit{2, "", String.concat([
      "error: invalid value '4294967296' for '--jobs <N>': expected a whole number from 0 to 4294967295\n",
      "\n",
      "Usage: argbench build [OPTIONS] <INPUT>...\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Job>}

law bad_format:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["build", "-f", "xml", "a"])
    == Cli.Quit{2, "", String.concat([
      "error: invalid value 'xml' for '--format <FMT>': expected one of 'text', 'json', 'csv'\n",
      "\n",
      "Usage: argbench build [OPTIONS] <INPUT>...\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Job>}

law no_input:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n), ["build"])
    == Cli.Quit{2, "", String.concat([
      "error: the following required arguments were not provided:\n",
      "  <INPUT>...\n",
      "\n",
      "Usage: argbench build [OPTIONS] <INPUT>...\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Job>}

law unknown_command:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n), ["buld", "a"])
    == Cli.Quit{2, "", String.concat([
      "error: unrecognized subcommand 'buld'\n",
      "\n",
      "  tip: a similar subcommand exists: 'build'\n",
      "\n",
      "Usage: argbench <COMMAND>\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Job>}

# build's options are not check's.
law other_options:
  {Cli.eval(~App.Job, ~App.decode, App.cli(), Cli.host(80n),
    ["check", "-v", "a"])
    == Cli.Quit{2, "", String.concat([
      "error: unexpected argument '-v' found\n",
      "\n",
      "  tip: to pass '-v' as a value, use '-- -v'\n",
      "\n",
      "Usage: argbench check [OPTIONS] <INPUT>...\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Job>}

# The line every peer prints: fields in declaration order, lists joined
# by commas, an empty list as nothing.
law line_build:
  {App.line(App.Build{2n, False{}, "out.bin", ["src", "lib"], 4, App.Json{},
    ["a.c", "b.c"]})
    == "build verbose=2 quiet=false output=out.bin include=src,lib jobs=4 format=json inputs=a.c,b.c"
    : String} &
  {App.line(App.Build{0n, True{}, "out", [], 1, App.Plain{}, ["a"]})
    == "build verbose=0 quiet=true output=out include= jobs=1 format=text inputs=a"
    : String} &
  {App.line(App.Build{1n, False{}, "o", ["i"], 0, App.Csv{}, ["a"]})
    == "build verbose=1 quiet=false output=o include=i jobs=0 format=csv inputs=a"
    : String}

law line_check:
  {App.line(App.Check{True{}, ["a", "b"]}) == "check strict=true inputs=a,b"
    : String} &
  {App.line(App.Check{False{}, ["a"]}) == "check strict=false inputs=a"
    : String}
