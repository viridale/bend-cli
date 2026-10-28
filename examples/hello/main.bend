# Purpose: the hello example shell: one call to Run.planned.
# Expected output: `bend examples/hello/main.bend -- Ada` prints
# `Hello, Ada!`. `--check-only` prints SOME PROOFS FAIL listing only defs
# that rely on sys.c and sys.js (F1).
# Run: bend examples/hello/main.bend -- --help

import Base
import ./app.bend as App
import ../../run.bend as Run

def main() -> IO(Unit):
  Run.planned(~App.Greeting, ~App.decode, ~App.plan, App.cli())
