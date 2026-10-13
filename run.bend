# Purpose: the public IO shell: probes the host, runs Cli.eval, writes its
# output, calls act and exits (§7). The host effects live in sys.c and
# sys.js; no law imports this file (F1).
# Expected output: SOME PROOFS FAIL, listing only the defs that rely on
# sys.c and sys.js (F1, G2).
# Run: bend run.bend --check-only

import Base
import ./cli.bend as Cli

# 1 if fd is a terminal, else 0.
def Sys.isatty(fd: U32) -> IO(U32):
  import "./sys.c"
  import "./sys.js"

# fd's terminal width in columns, or 0 if it has none.
def Sys.columns(fd: U32) -> IO(U32):
  import "./sys.c"
  import "./sys.js"

# Flushes stdout and ends the process with code; it does not return.
def Sys.exit(code: U32) -> IO(Unit):
  import "./sys.c"
  import "./sys.js"

def exit_when(zero: Bool, code: U32) -> IO(Unit):
  match zero:
    case True{}: IO.pure(Unit, Unit{})
    case False{}: Sys.exit(code)

# 0 returns, so work started with IO.fork can finish; any other code
# flushes stdout and ends the process at once.
def exit(+code: U32) -> IO(Unit):
  exit_when(U32.is_eq(code, 0), code)

def chomp_end(newline: Bool, c: Char) -> String:
  match newline:
    case True{}: SNil{}
    case False{}: SCon{c, SNil{}}

# c then t, less one final "\n".
def chomp_from(t: String, +c: Char) -> String:
  match t:
    case SNil{}: chomp_end(Char.is_eq(c, '\n'), c)
    case SCon{d, u}: SCon{c, chomp_from(u, d)}

# s less one final "\n": IO.print_err adds it back.
def chomp(s: String) -> String:
  match s:
    case SNil{}: SNil{}
    case SCon{c, t}: chomp_from(t, c)

def write_out(empty: Bool, out: String) -> IO(Unit):
  match empty:
    case True{}: IO.pure(Unit, Unit{})
    case False{}: IO.write(out)

def write_err(empty: Bool, err: String) -> IO(Unit):
  match empty:
    case True{}: IO.pure(Unit, Unit{})
    case False{}: IO.print_err(chomp(err))

# §7.2 step 4: out to stdout and err to stderr, each if not empty, then exit.
def finish(code: U32, +out: String, +err: String) -> IO(Unit):
  do IO<Unit>:
    write_out(String.is_empty(out), out)
    write_err(String.is_empty(err), err)
    exit(code)

def var_found(name: String,
    got: Result<&1, &1, U32 & String, String>) -> List<&2, Cli.Var>:
  match got:
    case Done{value}: [Cli.Var{name, value}]
    case Fail{e}: []

# Each set variable among names, in order.
def read_vars(names: List<&2, String>) -> IO(List<&2, Cli.Var>):
  match names:
    case Nil{}: IO.pure(List<&2, Cli.Var>, [])
    case +name <> tail:
      do IO<List<&2, Cli.Var>>:
        got : Result<&1, &1, U32 & String, String> <- IO.get_env(name)
        rest : List<&2, Cli.Var> <- read_vars(tail)
        return List.append(&2, Cli.Var, var_found(name, got), rest)

# §7.3: the variables c reads, whether stdout and stderr are TTYs, and their
# columns; Cli.probe decides the rest.
def host(c: Cli.Cmd) -> IO(Cli.Host):
  do IO<Cli.Host>:
    vars : List<&2, Cli.Var> <- read_vars(Cli.vars(c))
    out_tty : U32 <- Sys.isatty(1)
    err_tty : U32 <- Sys.isatty(2)
    out_cols : U32 <- Sys.columns(1)
    err_cols : U32 <- Sys.columns(2)
    return Cli.probe(vars, U32.is_eq(out_tty, 1), U32.is_eq(err_tty, 1),
      out_cols, err_cols)

def argv_list(args: List<String>) -> List<&2, String>:
  match args:
    case Nil{}: Nil{}
    case arg <> tail: arg <> argv_list(tail)

# IO.args without its head, the program as invoked.
def argv_of(args: List<String>) -> List<&2, String>:
  match args:
    case Nil{}: Nil{}
    case program <> tail: argv_list(tail)

# §7.2 step 5: act's code, mapped by Cli.act_exit.
def ended(r: (U32 & String)) -> IO(Unit):
  match r:
    case (code, err): finish(code, "", err)

def stepped(~A: Type, ~act: @+t: Cli.Term -> A -> IO(U32),
    s: Cli.Step<A>) -> IO(Unit):
  match s:
    case Cli.Quit{code, out, err}: finish(code, out, err)
    case Cli.Go{a, t}:
      do IO<Unit>:
        n : U32 <- act(t, a)
        ended(Cli.act_exit(n))

# §7.2: an app's whole main.
def main(~A: Type, ~decode: @+m: Cli.Matches -> Cli.Dec(A),
    ~act: @+t: Cli.Term -> A -> IO(U32), +c: Cli.Cmd) -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    h : Cli.Host <- host(c)
    stepped(~A, ~act, Cli.eval(~A, ~decode, c, h, argv_of(args)))
