# Purpose: the grep example shell: one call to Run.main.
# Expected output: `bend examples/grep/main.bend -- -m 1 Purpose
# examples/grep/main.bend` prints this file's first line. `--check-only`
# prints SOME PROOFS FAIL listing only defs that rely on sys.c and sys.js
# (F1).
# Run: bend examples/grep/main.bend -- --help

import Base
import ./app.bend as App
import ../../run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Grep, ~App.decode, ~App.act, App.cli())
