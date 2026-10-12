# Purpose: an app for as_f32 end to end (K8): one --rate <R> option; it
# prints the F32 it reads, as F32.show and as its bits.
# Expected output: `bend tests/f32.bend -- --rate 1.5` prints
# `1.5 1069547520`. `--check-only` prints SOME PROOFS FAIL listing only defs
# that rely on sys.c and sys.js (F1).
# Run: bend tests/f32.bend -- --rate 1.5

import Base
import ../cli.bend as Cli
import ../run.bend as Run

def cli() -> Cli.Cmd:
  Cli.cmd("f32", "Print a rate as read", [
    Cli.arg("--rate <R>", "The rate", [Cli.as_f32(), Cli.default("0")]),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(F32):
  Cli.f32(m, "rate")

def rate_text(+rate: F32) -> String:
  String.concat([F32.show(rate), " ", U32.show(F32.bits(rate))])

def act(+t: Cli.Term, rate: F32) -> IO(U32):
  do IO<U32>:
    IO.print(rate_text(rate))
    return 0

def main() -> IO(Unit):
  Run.main(~F32, ~decode, ~act, cli())
