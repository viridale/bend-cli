# Purpose: the pkg reference app shell: one call to Run.main (§12.3).
# Expected output: `bend main.bend -- list` prints
# `list all=false format=text verbose=0`. `--check-only` prints SOME PROOFS
# FAIL listing only defs that rely on sys.c and sys.js (F1).
# Run: bend main.bend -- --help

import Base
import ./demo.bend as Demo
import ./run.bend as Run

def main() -> IO(Unit):
  Run.main(~Demo.Action, ~Demo.decode, ~Demo.act, Demo.cli())
