# Changelog

## Unreleased

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

### Changed

- Bend 2.0.39 or newer is required.
- `Run.argv_of` takes the list `IO.args_bytes()` answers instead of
  `IO.args()`'s.

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
