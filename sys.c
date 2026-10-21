// Purpose: native host effects for run.bend: Sys.isatty and Sys.columns
// (§7.3). The compiler splices this file into a native build.
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

// A def the program never reaches has no id (bend guide effects), so each
// registration checks for its def's.
static void __attribute__((constructor)) sys_use(void) {
#ifdef CID(Sys.isatty)
  io_eff(CID(Sys.isatty), sys_isatty_run);
#endif
#ifdef CID(Sys.columns)
  io_eff(CID(Sys.columns), sys_columns_run);
#endif
}
