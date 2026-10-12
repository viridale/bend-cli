# `timeout`-like: run another command with its own options

`timeout` runs a program with a time limit, like GNU `timeout`. It shows:

- a wrapper whose last positional passes every token through to another
  program, options and `--` included;
- a value with its own syntax (`500ms`, `10s`, `2m`), parsed and rejected in
  the decoder with `Cli.fail`;
- `Process.run` with a time limit and an output limit;
- a family of exit statuses, mapped by a pure function with laws.

```console
$ timeout --help
Run a command with a time limit

Usage: timeout [OPTIONS] <DURATION> <COMMAND>...

Arguments:
  <DURATION>                Time limit: a whole number with an optional unit,
                            ms, s, m or h; seconds if none
  <COMMAND>...              The program to run, then its arguments

Options:
  -v, --verbose             Say on stderr when the time limit kills the command
      --max-output <BYTES>  Kill the command if it prints more than BYTES
                            [default: 16777216]
  -h, --help                Print help
  -V, --version             Print version

Examples:
  Give the tests ten seconds:
    $ timeout 10s make test
  Fail fast on a slow server:
    $ timeout 500ms curl -fsS https://example.com

Exit status: 124 if the time limit was reached, 125 if timeout itself failed,
126 if the command could not be run, 127 if it was not found, 2 for a usage
error; otherwise the command's own status.
```

## `app.bend`

```python
# Purpose: timeout, which runs another command with a time limit.
# Expected output: the command's own output; exit 124 if it ran out of time.
# Run: bend main.bend -- 2s sleep 5
import Base
import cli@1.0.0.0/cli.bend as Cli

type Call is Data:
  Call{program: String, args: List<&2, String>}

type Limit is Data:
  Limit{ms: U32, max_output: U32, verbose: Bool, call: Call}

def cli() -> Cli.Cmd:
  Cli.cmd("timeout", "Run a command with a time limit", [
    Cli.version("1.0.0"),
    Cli.arg("-v, --verbose", "Say on stderr when the time limit kills the command", []),
    Cli.arg("--max-output <BYTES>", "Kill the command if it prints more than BYTES",
      [Cli.as_u32(), Cli.default("16777216")]),
    Cli.arg("<DURATION>", "Time limit: a whole number with an optional unit, ms, s, m or h; seconds if none", []),
    Cli.arg("<COMMAND>...", "The program to run, then its arguments", [Cli.rest()]),
    Cli.example("timeout 10s make test", "Give the tests ten seconds"),
    Cli.example("timeout 500ms curl -fsS https://example.com", "Fail fast on a slow server"),
    Cli.after("Exit status: 124 if the time limit was reached, 125 if timeout itself failed, 126 if the command could not be run, 127 if it was not found, 2 for a usage error; otherwise the command's own status."),
  ])

# Durations: "500ms", "10s", "2m", "1h", or "10" for seconds.

def times(n: Maybe<&2, U32>, +k: U32) -> Maybe<&2, U32>:
  match n:
    case None{}:
      None{}
    case Some{+v}:
      Bool.pick(Maybe<&2, U32>, U32.is_eq(U32.div(U32.mul(v, k), k), v),
        Some{U32.mul(v, k)}, None{})

# The number before a unit of n characters, times k.
def cut(+text: String, n: Nat, k: U32) -> Maybe<&2, U32>:
  times(U32.read(String.take(text, Nat.sub(String.length(text), n))), k)

def hours(hit: Bool, +text: String) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      cut(text, 1n, 3600000)
    case False{}:
      times(U32.read(text), 1000)

def minutes(hit: Bool, +text: String) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      cut(text, 1n, 60000)
    case False{}:
      hours(String.ends_with(text, "h"), text)

def seconds(hit: Bool, +text: String) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      cut(text, 1n, 1000)
    case False{}:
      minutes(String.ends_with(text, "m"), text)

def millis_if(hit: Bool, +text: String) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      cut(text, 2n, 1)
    case False{}:
      seconds(String.ends_with(text, "s"), text)

def millis(+text: String) -> Maybe<&2, U32>:
  millis_if(String.ends_with(text, "ms"), text)

def above_zero(zero: Bool, ms: U32) -> Cli.Dec(U32):
  match zero:
    case True{}:
      Cli.fail(U32, "the time limit must be above zero")
    case False{}:
      Cli.Dec.pure(U32, ms)

def checked(+text: String, found: Maybe<&2, U32>) -> Cli.Dec(U32):
  match found:
    case None{}:
      Cli.fail(U32, ("invalid duration '" ++ text ++ "': use a whole number with an optional unit, such as 500ms, 10s, 2m or 1h" : String))
    case Some{+ms}:
      above_zero(U32.is_zero(ms), ms)

def duration(+text: String) -> Cli.Dec(U32):
  checked(text, millis(text))

def call(command: List<&2, String>) -> Cli.Dec(Call):
  match command:
    case Nil{}:
      Cli.fail(Call, "a command is required")
    case program <> args:
      Cli.Dec.pure(Call, Call{program, args})

def decode(+m: Cli.Matches) -> Cli.Dec(Limit):
  do Cli.Dec<Limit>:
    verbose : Bool <- Cli.flag(m, "verbose")
    max_output : U32 <- Cli.u32(m, "max-output")
    text : String <- Cli.str(m, "duration")
    command : List<&2, String> <- Cli.strs(m, "command")
    ms : U32 <- duration(text)
    c : Call <- call(command)
    return Limit{ms, max_output, verbose, c}

# Exit statuses. Process.run fails with ETIMEDOUT (60 on macOS, 110 on Linux)
# after killing the command, EFBIG (27) after killing it for too much output,
# ENOENT (2) if it does not exist and EACCES (13) if it cannot be executed.

def timed_out(+code: U32) -> Bool:
  Bool.or(U32.is_eq(code, 60), U32.is_eq(code, 110))

def status(+code: U32) -> U32:
  Bool.pick(U32, timed_out(code), 124,
    Bool.pick(U32, U32.is_eq(code, 2), 127,
      Bool.pick(U32, U32.is_eq(code, 13), 126, 125)))

def killed(verbose: Bool, +program: String) -> String:
  match verbose:
    case True{}:
      ("timeout: '" ++ program ++ "' reached the time limit and was killed" : String)
    case False{}:
      ""

# What to print on stderr when the command did not finish on its own.
def failure(verbose: Bool, +program: String, +code: U32, msg: String) -> String:
  Bool.pick(String, timed_out(code), killed(verbose, program),
    Bool.pick(String, U32.is_eq(code, 27),
      ("timeout: '" ++ program ++ "' printed more than --max-output allows and was killed" : String),
      ("timeout: failed to run '" ++ program ++ "': " ++ msg : String)))

# Running.

# Stderr writes always end in a newline, so drop the command's own.
def chomp(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      match t:
        case SNil{}:
          Bool.pick(String, Char.is_eq(h, '\n'), SNil{}, SCon{h, SNil{}})
        case SCon{h2, t2}:
          SCon{h, chomp(SCon{h2, t2})}

def to_err(err: String) -> IO(Unit):
  match err:
    case SNil{}:
      IO.pure(Unit, Unit{})
    case SCon{h, t}:
      IO.print_err(chomp(SCon{h, t}))

def Ran() -> Type:
  Result<&1, &1, U32 & String, U32 & (String & String)>

def ran(verbose: Bool, +program: String, r: Ran()) -> IO(U32):
  match r:
    case Done{(code, (out, err))}:
      do IO<U32>:
        IO.write(out)
        to_err(err)
        return code
    case Fail{(+code, msg)}:
      do IO<U32>:
        to_err(failure(verbose, program, code, msg))
        return status(code)

# Process.run takes a List<String>; argv values are List<&2, String>.
def loose(xs: List<&2, String>) -> List<String>:
  match xs:
    case Nil{}:
      []
    case h <> t:
      h <> loose(t)

def act(+t: Cli.Term, l: Limit) -> IO(U32):
  match l:
    case Limit{ms, max_output, verbose, c}:
      match c:
        case Call{+program, args}:
          IO.bind(Ran(), U32, Process.run(program, loose(args), "", max_output, ms),
            ran(verbose, program))
```

Notes:

- **The program name is part of the pass-through slot.** `<COMMAND>...`
  with `Cli.rest()` makes every token from the program name on a value. A
  separate `<COMMAND>` slot followed by `[ARGS]...` looks equivalent but is
  not: the first token after the program name is still scanned, so
  `timeout 5s ls --help` would print `timeout`'s help instead of passing
  `--help` to `ls`. With one slot, `ls` starts the rest and `--help` is
  `ls`'s.
- **Where `timeout`'s options may go.** Anywhere before the program name:
  `timeout -v 5s sleep 9` and `timeout 5s -v sleep 9` are the same. From
  the program name on, every token belongs to the program, so
  `timeout 5s sleep 9 -v` passes `-v` to `sleep`.
- **Syntax checks live in the decoder.** `<DURATION>` is a plain string to
  the parser. `duration` turns it into milliseconds or calls `Cli.fail`,
  which prints the message in the library's usage-error shape and exits 2.
  The unit helpers are a chain of small defs, because a `match` needs a
  parameter, not a computed value.
- **Statuses.** GNU `timeout` exits 125 when it fails itself, including on a
  usage error. A bend-cli app always exits 2 on a usage error, so this
  `timeout` documents 2 for usage errors and uses 125 only for failures
  while running.
- **Output.** `Process.run` collects the command's output and returns it
  when the command ends, so it is not streamed, the command's stdin is
  empty, and output from a command that was killed is lost. `--max-output`
  bounds the memory used.
- **The runtime's `--`.** Bend removes the first `--` from argv before
  `main` runs, so `timeout 5s grep -- -x f` reaches `grep` as
  `grep -x f`. Users type `timeout 5s grep -- -- -x f`
  ([Platform notes](../concepts/platform.md#the-runtime-takes-the-first---)).

## `main.bend`

```python
# Purpose: the timeout shell.
# Expected output: the command's own output; exit 124 if it ran out of time.
# Run: bend main.bend -- 2s sleep 5
import Base
import ./app.bend as App
import cli@1.0.0.0/run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Limit, ~App.decode, ~App.act, App.cli())
```

## `LAWS.bend`

```python
# Purpose: laws for timeout: the definition, pass-through, durations and statuses.
# Expected output: one TODO per law until PROOF.bend proves them.
# Run: bend LAWS.bend --check-only
import Base
import ./app.bend as App
import cli@1.0.0.0/cli.bend as Cli

law cli_ok:
  {Cli.check(~App.Limit, ~App.decode, App.cli()) == [] : List<&2, Cli.Problem>}

law pass_through:
  {Cli.eval(~App.Limit, ~App.decode, App.cli(), Cli.host(80n),
      ["-v", "2m", "ls", "--help", "-v", "--", "x"])
    == Cli.Go{App.Limit{120000, 16777216, True{},
                App.Call{"ls", ["--help", "-v", "--", "x"]}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Limit>}

law bad_duration:
  {Cli.eval(~App.Limit, ~App.decode, App.cli(), Cli.host(80n), ["5x", "ls"])
    == Cli.Exit{2, "", "error: invalid duration '5x': use a whole number with an optional unit, such as 500ms, 10s, 2m or 1h\n\nUsage: timeout [OPTIONS] <DURATION> <COMMAND>...\n\nFor more information, try '--help'.\n"}
    : Cli.Step<App.Limit>}

law durations:
  {[App.millis("500ms"), App.millis("10s"), App.millis("2m"), App.millis("1h"), App.millis("7")]
    == [Some{500}, Some{10000}, Some{120000}, Some{3600000}, Some{7000}]
    : List<&2, Maybe<&2, U32>>}

law bad_durations:
  {[App.millis("1.5s"), App.millis("s"), App.millis("10x"), App.millis("5000h")]
    == [None{}, None{}, None{}, None{}] : List<&2, Maybe<&2, U32>>}

law statuses:
  {[App.status(60), App.status(110), App.status(2), App.status(13), App.status(27)]
    == [124, 124, 127, 126, 125] : List<&2, U32>}

law quiet_timeout:
  {App.failure(False{}, "sleep", 60, "Operation timed out") == "" : String}

law too_loud:
  {App.failure(False{}, "yes", 27, "File too large")
    == "timeout: 'yes' printed more than --max-output allows and was killed" : String}
```

`5000h` is rejected because it does not fit in a `U32` of milliseconds.

## `PROOF.bend`

```python
# Purpose: proofs of the timeout laws.
# Expected output: ALL PROOFS CHECK
# Run: bend PROOF.bend
import Base
import ./LAWS.bend as Laws

def Laws.cli_ok():
  {==}

def Laws.pass_through():
  {==}

def Laws.bad_duration():
  {==}

def Laws.durations():
  {==}

def Laws.bad_durations():
  {==}

def Laws.statuses():
  {==}

def Laws.quiet_timeout():
  {==}

def Laws.too_loud():
  {==}
```

## Running it

```console
$ bend main.bend -o timeout
$ ./timeout -v 500ms sleep 2
timeout: 'sleep' reached the time limit and was killed
$ ./timeout 5s sh -c 'echo hi; exit 3'
hi
$ ./timeout 5s no-such-program
timeout: failed to run 'no-such-program': No such file or directory
$ ./timeout 5x ls
error: invalid duration '5x': use a whole number with an optional unit, such as 500ms, 10s, 2m or 1h

Usage: timeout [OPTIONS] <DURATION> <COMMAND>...

For more information, try '--help'.
```

Exit statuses, in order: 124, 3, 127, 2.
