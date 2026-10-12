# Platform notes

The Bend runtime handles argv, output and exit before and after your program
runs. This page lists what it does that a CLI author will notice, and how
bend-cli works with or around it. Facts are checked against Bend 2.0.36.

## The runtime takes the first `--`

A native build and compiled JavaScript both remove the first `--` from argv
before `main` runs, and pass everything after it through unchanged. The
program never sees that `--`.

So when a user wants the CLI's own end-of-options marker, they type it
twice:

```
$ rm -- -- -file
```

The runtime removes the first `--`; bend-cli sees `["--", "-file"]` and treats
`-file` as a positional.

Running from source is different. `bend main.bend args` rejects any option
before a `--`, so there you always write one `--` to separate Bend's options
from your app's, and a second one for your app:

```
$ bend main.bend -- -- -file
```

Error tips print the POSIX form (`use '-- -file'`), which is one `--` short
in native and JavaScript builds today. Tell your users about the doubled `--` in
your own README, or design so they rarely need it: a `rest()` positional
already passes everything after it through, `--` included
([Wrappers](../how-to/wrappers.md)).

This is tracked upstream as
[bendlang/bend#1466](https://github.com/bendlang/bend/issues/1466).

## Reserved runtime options

| Option | Removed by native | Removed by compiled JS |
|---|---|---|
| `--threads N` | yes | yes |
| `--gpu V` | yes | yes |
| `--gpu-build` | yes | no |
| `--bend-help` | yes | yes |

They are removed anywhere they appear before the first `--`, including where
your app expected a value: in `grep -e --threads`, the runtime takes
`--threads` and the following token. Do not declare these names, and do not
use them as values in tests. bend-cli does not reserve them, so a definition
that declares `--threads` passes `Cli.check`, but the option can never reach
the program in a native build.

## Exit codes

- Exit codes wrap modulo 256 in the runtime, so 256 would exit 0. `Run.main`
  catches an `act` result above 255, prints
  `bug: exit code <n> is out of range 0..255` and exits 70.
- `IO.die` always writes a line to stderr, even for an empty message, so
  `run.bend` has a small host effect, `Sys.exit`, to exit silently. It goes
  away once Bend's `main` can return an exit status
  ([bendlang/bend#1465](https://github.com/bendlang/bend/issues/1465), fixed,
  not yet released).
- An exit of 0 returns from `main` normally, so work started with `IO.fork`
  finishes. Any other code ends the process at once.

## Closed pipes

On Bend 2.0.36, writing to a closed stdout pipe (`app list | head -1`) prints
`bend: a short write on a standard stream` and exits 1. The fix
([bendlang/bend#1470](https://github.com/bendlang/bend/pull/1470)) ends the
program by SIGPIPE instead, as C programs do; it is merged but not yet
released.

## Terminal probing

Whether stdout and stderr are terminals, and the terminal's width, come from
two host effects in `sys.c` and `sys.js`. Bend's Base library declined to add
terminal queries, so these effects are permanent. Because they are foreign
code, no law may import `main.bend`, and `bend main.bend --verdict` fails;
laws import your pure `app.bend` instead
([Architecture](architecture.md)).

## Text

- **Width is per code point.** East Asian wide characters count 2 columns and
  combining marks 0, using Unicode 15.1 tables. Grapheme clusters are not
  segmented, so emoji joined with U+200D and flag pairs can misalign help
  columns.
- **Invalid UTF-8 becomes U+FFFD.** The runtime decodes argv as UTF-8, so a
  file name with raw non-UTF-8 bytes cannot be passed through unchanged.
- **Output always ends in one newline.** Bend's `IO.print_err` adds a
  newline and nothing writes to stderr without one, so the library renders
  text with exactly one trailing newline and strips it before writing
  stderr.

## Reading stdin

`File.open("/dev/stdin", "r")` reads standard input in native builds and in
compiled JavaScript. bend-cli treats `-` as an ordinary positional; your
`act` decides that `-` means stdin ([Positionals](../how-to/positionals.md)).

## Support

CI runs on macOS arm64 and Ubuntu 24.04 x86-64. Native builds need clang;
compiled JavaScript needs Bun 1.1 or newer. Windows is out of scope for 1.x.
