// Purpose: JavaScript host effects for run.bend: Sys.isatty, Sys.columns and
// Sys.exit (§7.3), for -o x.js builds and `bend x.bend`.
// Expected output: none; it registers effects.
// Run: bend main.bend -o build/pkg.js

function sys_isatty(fd) {
  return require("tty").isatty(fd) ? 1 : 0;
}

// 0 when fd is not a terminal or reports no size.
function sys_columns(fd) {
  const stream = fd === 1 ? process.stdout : fd === 2 ? process.stderr : null;
  return (stream && stream.columns) || 0;
}

// Output is written synchronously, so nothing is pending at exit.
function sys_exit(code) {
  process.exit(code);
}

io_eff(CID(Sys.isatty), sys_isatty);
io_eff(CID(Sys.columns), sys_columns);
io_eff(CID(Sys.exit), sys_exit);
