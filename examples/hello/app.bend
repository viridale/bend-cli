# Purpose: the hello example app, pure part: the README quickstart's command
# definition, decoder and plan.
# Expected output: ALL PROOFS CHECK.
# Run: bend examples/hello/app.bend --check-only

import Base
import ../../cli.bend as Cli

type Greeting is Data:
  Greeting{name: String}

def cli() -> Cli.Cmd:
  Cli.cmd("hello", "Print a greeting", [
    Cli.arg("[NAME]", "Who to greet", [Cli.default("world")]),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(Greeting):
  do Cli.Dec<Greeting>:
    name : String <- Cli.str(m, "name")
    return Greeting{name}

def plan(+t: Cli.Term, greeting: Greeting) -> Cli.Ran:
  match greeting:
    case Greeting{name}: Cli.Ran{0, ("Hello, " ++ name ++ "!\n" : String), ""}
