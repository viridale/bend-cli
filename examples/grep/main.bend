# Purpose: the grep example shell.
# Expected output: SOME PROOFS FAIL, listing only the defs that rely on
# run.bend's sys.c and sys.js (F1, G2).
# Run: bend examples/grep/main.bend --check-only

import Base
import ./app.bend as App
import ../../run.bend as Run
