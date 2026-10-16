# Purpose: an app that calls Run.host and Cli.eval itself and exits by
# IO.die, so it reaches Sys.isatty and Sys.columns but never Sys.exit; its
# native build fails unless sys.c registers only the effects a program
# reaches. It prints NAME and the width Run.host probed.
# Expected output: `COLUMNS=100 bend tests/host.bend -- Ada` prints
# `Ada 100`. `--check-only` prints SOME PROOFS FAIL listing only defs that
# rely on sys.c and sys.js (F1).
# Run: COLUMNS=100 bend tests/host.bend -- Ada

import Base
import ../cli.bend as Cli
import ../run.bend as Run

def cli() -> Cli.Cmd:
  Cli.cmd("host", "Print a name and the help width", [
    Cli.arg("[NAME]", "The name", [Cli.default("world")]),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(String):
  Cli.str(m, "name")

def named(t: Cli.Term, name: String) -> String:
  match t:
    case Cli.Term{out_color, err_color, width}:
      String.concat([name, " ", Nat.show(width)])

# err as Run.finish writes it, then any other code than 0 by IO.die, which
# adds the "\n" chomp takes.
def quit(zero: Bool, code: U32, +err: String) -> IO(Unit):
  match zero:
    case True{}: Run.write_err(String.is_empty(err), err)
    case False{}: IO.die(Unit, code, Run.chomp(err))

def stepped(s: Cli.Step<String>) -> IO(Unit):
  match s:
    case Cli.Go{name, t}: IO.print(named(t, name))
    case Cli.Quit{+code, +out, err}:
      do IO<Unit>:
        Run.write_out(String.is_empty(out), out)
        quit(U32.is_eq(code, 0), code, err)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    h : Cli.Host <- Run.host(cli())
    stepped(Cli.eval(~String, ~decode, cli(), h, Run.argv_of(args)))
