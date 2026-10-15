# Purpose: the argbench example shell: one call to Run.main.
# Expected output: `bend examples/argbench/main.bend -- build -vv -j 4 a.c`
# prints `build verbose=2 quiet=false output=out include= jobs=4
# format=text inputs=a.c`. `--check-only` prints SOME PROOFS FAIL listing
# only defs that rely on sys.c and sys.js (F1).
# Run: bend examples/argbench/main.bend -- --help

import Base
import ./app.bend as App
import ../../run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Job, ~App.decode, ~App.act, App.cli())
