# Purpose: the hello example app, pure part: the README quickstart's command
# definition, decoder and action.
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

def act(+t: Cli.Term, greeting: Greeting) -> IO(U32):
  match greeting:
    case Greeting{name}:
      do IO<U32>:
        IO.print(("Hello, " ++ name ++ "!" : String))
        return 0
