# Usage strings

The first argument of `Cli.arg` declares the argument's names, whether it
takes a value, and how many times it may appear. Help shows it exactly as
written.

## Forms

| Usage string | Kind | Value when given | When absent |
|---|---|---|---|
| `-v`, `--verbose`, `-v, --verbose` | flag | `True` | `False` |
| `-v, --verbose...` | count | number of occurrences | `0n` |
| `--[no-]x`, `-x, --[no-]x` | negatable | `--x`, `-x` → `True`; `--no-x` → `False`; last wins | default, else `False` |
| names` <V>` | option | the last occurrence | default, else none |
| names` <V>...` | list option | every occurrence, in order | default, else `[]` |
| `--long[=<V>]` | optional-value option | `--long=v` → v; `--long` → the `bare` value | default, else none |
| `<P>` | required positional | one token | error |
| `[P]` | optional positional | one token | default, else none |
| `<P>...` | variadic, one or more | tokens, in order | error |
| `[P]...` | variadic, zero or more | tokens, in order | default, else `[]` |

"names" is `-s`, `--long` or `-s, --long`.

## Grammar

No spaces are allowed beyond the ones shown.

```
usage      = option | positional
option     = names [value] [repeat]
names      = short | short ", " long | long
short      = "-" SC
long       = "--" ["[no-]"] NAME
value      = " <" PH ">" | "[=<" PH ">]"
positional = ( "<" PH ">" | "[" PH "]" ) [repeat]
repeat     = "..."
SC         = an ASCII letter or digit
NAME       = (ASCII letter | digit) { ASCII letter | digit | "-" | "_" | "." }
PH         = one or more characters, none of: space < > [ ] =
```

- `NAME` may not end in `.`. A trailing `...` is always `repeat`: `--quiet...`
  is a count named `--quiet`.
- `[no-]` goes only on a long name without a value.
- `[=<V>]` goes only on a long-only option and requires `Cli.bare(v)`.

## Ids

An argument's id is what readers and relations use:

1. `Cli.id("x")` if given;
2. else the long name without `--`, and without `[no-]` for a negatable switch (`--no-clobber` has id `no-clobber`);
3. else the short letter;
4. else the placeholder in lower case.

| Usage | Id |
|---|---|
| `-v, --verbose...` | `verbose` |
| `-C <DIR>` | `C` |
| `--[no-]cache` | `cache` |
| `<FILE>...` | `file` |
| `--max-count <NUM>` | `max-count` |

Ids are unique within a scope (a command and the globals it inherits).

## Errors in usage strings

A malformed usage string is a `BadUsage{at, usage, col}` problem, where `col`
is the 0-based index of the first character that breaks the grammar (the
length of the string when it ends too early):

| Usage | col | Why |
|---|---|---|
| `--out <FILE` | 11 | the placeholder is not closed by `>` |
| `-ab` | 2 | a short name is one character |
| `--quiet.` | 7 | a name cannot end in `.` |
| `-o,--out` | 2 | the separator is `", "` |
| `--color=<W>` | 7 | an attached value is written `[=<W>]` |
| `--[no-]x <V>` | 8 | a negatable takes no value |

## In help and errors

Help shows the string as written. Errors name an argument by its usage string
without the short name when it has both: `-n, --times <N>` appears as
`--times <N>`, `-o <FILE>` as `-o <FILE>`, `<SRC>...` as `<SRC>...`.
