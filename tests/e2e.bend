# Purpose: end-to-end runner: each case in tests/cases.bend through env(1)
# in the native, js and dev modes, comparing status, stdout and stderr
# exactly (§13). Run it from the repository root after building build/pkg,
# build/pkg.js, build/f32, build/f32.js, build/host and build/host.js (G4).
# Expected output: `e2e: N runs passed`, exit 0; otherwise a FAIL block per
# failing run and exit 1. `--check-only` prints ALL PROOFS CHECK.
# Run: bend tests/e2e.bend

import Base
import ./cases.bend as Cases

# How a mode starts an app; dash adds the launcher's "--" (K1). Bun removes
# a "--" right after the script path (F19), so the js launchers end in one.
type Mode is Data:
  Mode{name: String, launcher: List<&2, String>, dash: Bool}

# One process to run: env(1)'s arguments and what the case expects.
type Job is Data:
  Job{label: String, args: List<&2, String>, code: U32, out: String,
    err: String}

def modes(native: String, js: String, dev: String) -> List<&2, Mode>:
  [
    Mode{"native", [native], True{}},
    Mode{"js", ["bun", js, "--"], True{}},
    Mode{"dev", ["bend", dev], True{}},
  ]

def canary_modes() -> List<&2, Mode>:
  [
    Mode{"native", ["build/pkg"], False{}},
    Mode{"js", ["bun", "build/pkg.js", "--"], False{}},
  ]

def dashed(dash: Bool) -> List<&2, String>:
  match dash:
    case True{}: ["--"]
    case False{}: []

def job(path: String, m: Mode, c: Cases.Case) -> Job:
  match m c:
    case Mode{name, launcher, dash}
        Cases.Case{case_name, env, argv, code, out, err}:
      Job{String.concat([name, ": ", case_name]),
        List.concat(&2, String, [["-i", String.append("PATH=", path)], env,
          launcher, dashed(dash), argv]),
        code, out, err}

def mode_jobs(cases: List<&2, Cases.Case>, +path: String, +m: Mode) ->
    List<&2, Job>:
  match cases:
    case Nil{}: Nil{}
    case c <> tail: job(path, m, c) <> mode_jobs(tail, path, m)

# Every case in every mode, mode by mode.
def all_jobs(ms: List<&2, Mode>, +cases: List<&2, Cases.Case>,
    +path: String) -> List<&2, Job>:
  match ms:
    case Nil{}: Nil{}
    case m <> tail:
      List.append(&2, Job, mode_jobs(cases, path, m),
        all_jobs(tail, cases, path))

def jobs(+path: String) -> List<&2, Job>:
  List.concat(&2, Job, [
    all_jobs(modes("build/pkg", "build/pkg.js", "main.bend"), Cases.cases(),
      path),
    all_jobs(canary_modes(), Cases.canaries(), path),
    all_jobs(modes("build/f32", "build/f32.js", "tests/f32.bend"),
      Cases.f32_cases(), path),
    all_jobs(modes("build/host", "build/host.js", "tests/host.bend"),
      Cases.host_cases(), path),
  ])

def strict(xs: List<&2, String>) -> List<String>:
  match xs:
    case Nil{}: Nil{}
    case x <> tail: x <> strict(tail)

def esc_pick(newline: Bool, escape: Bool, c: Char) -> String:
  match newline escape:
    case True{} _: "\\n"
    case False{} True{}: "\\e"
    case False{} False{}: SCon{c, SNil{}}

# s with each newline as \n and each ESC as \e, so a mismatch shows every
# byte on one line.
def esc(s: String) -> String:
  match s:
    case SNil{}: SNil{}
    case SCon{+c, t}:
      String.append(esc_pick(Char.is_eq(c, '\n'), Char.is_eq(c, '\u{1B}'), c),
        esc(t))

def differs(same: Bool, what: String, want: String, got: String) ->
    List<&2, String>:
  match same:
    case True{}: []
    case False{}:
      [String.concat(["  ", what, ": expected \"", esc(want), "\", got \"",
        esc(got), "\""])]

def text_diff(what: String, +want: String, +got: String) -> List<&2, String>:
  differs(String.eq(want, got), what, want, got)

def code_diff(+want: U32, +got: U32) -> List<&2, String>:
  differs(U32.is_eq(want, got), "status", U32.show(want), U32.show(got))

# A FAIL block for label, or None if nothing differs.
def failure(label: String, diffs: List<&2, String>) -> Maybe<&2, String>:
  match diffs:
    case Nil{}: None{}
    case diff <> tail:
      Some{String.join(String.append("FAIL ", label) <> diff <> tail, "\n")}

def judged(label: String, code: U32, out: String, err: String,
    got: Result<&1, &1, U32 & String, U32 & (String & String)>) ->
    Maybe<&2, String>:
  match got:
    case Fail{(n, msg)}:
      Some{String.concat(["FAIL ", label, "\n  did not run: ", msg])}
    case Done{(status, (got_out, got_err))}:
      failure(label, List.concat(&2, String, [code_diff(code, status),
        text_diff("stdout", out, got_out), text_diff("stderr", err, got_err)]))

def reported(found: Maybe<&2, String>) -> IO(Nat):
  match found:
    case None{}: IO.pure(Nat, 0n)
    case Some{block}:
      do IO<Nat>:
        IO.print(block)
        return 1n

# Runs each job in turn, printing each failure as it happens; the number
# that failed.
def run_jobs(js: List<&2, Job>) -> IO(Nat):
  match js:
    case Nil{}: IO.pure(Nat, 0n)
    case Job{label, args, code, out, err} <> tail:
      do IO<Nat>:
        got : Result<&1, &1, U32 & String, U32 & (String & String)> <-
          Process.run("/usr/bin/env", strict(args), "", 1048576, 10000)
        failed : Nat <- reported(judged(label, code, out, err, got))
        rest : Nat <- run_jobs(tail)
        return (failed + rest : Nat)

def verdict(none: Bool, failed: Nat, total: Nat) -> IO(Unit):
  match none:
    case True{}:
      IO.print(String.concat(["e2e: ", Nat.show(total), " runs passed"]))
    case False{}:
      IO.die(Unit, 1, String.concat(["e2e: ", Nat.show(failed), " of ",
        Nat.show(total), " runs failed"]))

def finish(+failed: Nat, total: Nat) -> IO(Unit):
  verdict(Nat.is_eq(failed, 0n), failed, total)

def run_all(+all: List<&2, Job>) -> IO(Unit):
  do IO<Unit>:
    failed : Nat <- run_jobs(all)
    finish(failed, List.length(&2, Job, all))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("PATH"))
    run_all(jobs(path))
