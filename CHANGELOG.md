# Changelog

## Unreleased

### Added

- `Cli.usage_status(n)` on the root command ends its usage errors with exit
  status `n`, from 1 to 255, instead of 2, for wrappers such as `timeout`
  that keep the low codes for their child; `Cli.usage_code(c)` returns the
  status. P10 and P11 now range over it (#45).
- `Cli.Style` adds `Italic`, `Reverse`, the background colors `BgRed` to
  `BgCyan`, the 256-color `Fg256{n}` and `Bg256{n}`, and the RGB
  `FgRgb{r, g, b}` and `BgRgb{r, g, b}` for `Cli.paint` and `Cli.emit`; an
  index or a color part above 255 is written as 255. P1 and P2 cover them,
  and a `match` on `Cli.Style` needs their arms (#39).

### Changed

- `Cli.check` also decodes each path's sample with one argument at a time in
  each of its other states: left out unless it is required or has a default,
  and given each of its `Cli.one_of` values, both states of a negatable flag
  or a `Cli.as_bool()` value, or a value of its type in place of a default. A
  decoder bug behind a branch on another argument's value is now reported,
  each message once per path; P21 covers every state check tries (#64).
  A `{==}` proof of `Cli.check(...) == []` takes more of `--verdict`'s fuel:
  the pkg demo's now goes a path at a time.

## 0.2.0.0

### Added

- `Cli.arg_text` decodes an argument's bytes, turning each byte that starts
  no well-formed UTF-8 sequence into U+DC00 plus the byte (PEP 383), and
  `Cli.arg_bytes` gives the bytes back. `Run.main` reads `argv` through
  them, so a native app can open a file whose name is not UTF-8 with
  `File.open_bytes` (#66).
- `Run.planned` runs an app whose action is a pure `plan(term, value)`
  returning a `Cli.Ran{code, out, err}`: its exit status and its stdout and
  stderr text. `Cli.invoke` returns the `Cli.Ran` that `Run.planned` writes
  and exits with for an `argv`, so a law can state what the app prints. The
  quickstart, `examples/hello` and the pkg demo now use a plan (#41).
- `Cli.program` reads a `<COMMAND>...` positional with `Cli.rest()` as a
  `Cli.Program{name, args}`, a program and its arguments in one slot, as
  `timeout` and `env` take them; `Cli.program_opt` reads `[COMMAND]...`
  (#43).
- `Cli.unknown_text(c, path, name, t)` renders the error `Cli.eval` gives an
  unknown subcommand, with similar names and usage, so an app with
  `Cli.external()` can report a name that no plugin answers to (#44).

### Changed

- Bend 2.0.39 or newer is required.
- `Run.argv_of` takes the list `IO.args_bytes()` answers instead of
  `IO.args()`'s.
- A `Cli.rest()` positional's first value may start with `-`, as a
  `Cli.hyphen()` positional's may, so `retry curl -fsS url` passes `-fsS` on
  instead of failing on `-f` (#42).
- A `Cli.hyphen()` positional takes a long token that names no option, such
  as `--x=1`, as it takes `-x`.
- A huge argv parses faster: argbench's `build` with 10,000 `-I` pairs and
  as many inputs takes 42.8 ms in a native app, where 0.1.0.0 took 59.8
  (median wall time on an Apple M3 Max; README, Performance).

### Output changes

- In a native app, an argument cut short in the middle of a UTF-8 sequence
  prints one U+FFFD for each of its bytes: `E2 82` printed one before and
  prints two now. Compiled JavaScript is unchanged.

## 0.1.0.0

### Added

- Pure command definitions, parsing, typed decoding, validation, and source
  tracking.
- Summary and full help, usage errors with suggestions, color, and version
  output.
- Bash, zsh, and fish completions and man pages.
- IO shell for native and compiled-JavaScript applications.
- Example applications, laws, end-to-end cases, and a benchmark.
- A benchmark against clap, cobra, argparse, and commander: the same command
  in each, checked against a Bend example and timed by `tools/peerbench.sh`.

### Output changes

- Initial release; there is no prior output contract.
