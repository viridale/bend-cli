// Purpose: native host effects for run.bend: Sys.isatty, Sys.columns and
// Sys.exit (§7.3). The compiler splices this file into a native build.
// Expected output: none; it registers effects.
// Run: bend main.bend -o build/pkg

#include <sys/ioctl.h>

Term sys_isatty_run(Env e, Term* f, IoWork* w) {
  return (Term)(u32)(isatty((int)(u32)f[0]) == 1);
}

// 0 when fd is not a terminal or reports no size.
Term sys_columns_run(Env e, Term* f, IoWork* w) {
  struct winsize ws;
  int ok = ioctl((int)(u32)f[0], TIOCGWINSZ, &ws) == 0;
  return (Term)(u32)(ok ? ws.ws_col : 0);
}

// io_sync flushes stdout and fails loudly on a short write; exit wraps the
// code modulo 256 (F16), so Run.main passes only 0..255.
Term sys_exit_run(Env e, Term* f, IoWork* w) {
  io_sync();
  exit((int)(u32)f[0]);
}

static void __attribute__((constructor)) sys_use(void) {
  io_eff(CID(Sys.isatty), sys_isatty_run);
  io_eff(CID(Sys.columns), sys_columns_run);
  io_eff(CID(Sys.exit), sys_exit_run);
}
