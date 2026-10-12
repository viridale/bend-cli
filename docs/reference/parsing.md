# Parsing rules

`Cli.eval(c, host, argv)` decides in this order: check the definition, scan
argv, resolve sources and positionals, check relations, decode. This page
is the precise version; the [how-to guides](../README.md#how-to-guides)
explain the same rules by task.

## Scope

At each command path, the names in scope are:

- the command's own arguments;
- the `global()` arguments of every ancestor;
- the built-ins: `--help` (and `-h` unless a user argument has it);
  `--version` on the root when `version` is set (and `-V` unless taken);
  the `help` subcommand on commands that have subcommands.

Names, ids and subcommand names are unique within a scope.

## Scanning

Tokens are read left to right. For each token, the first matching rule
applies.

| # | Token | Action |
|---|---|---|
| R0 | after `--`, or inside a `rest()` positional | a positional; no subcommand lookup |
| R1 | `--` | end of options |
| R2 | `--name` or `--name=value` | look up `name` among long names in scope; unknown is E01. A flag, count or switch given `=value` is E05. An option takes `value`, which may be empty, else the next token (R6). An optional-value option takes `value`, else its `bare` value. `--no-x` sets switch `x` to `False`. |
| R3 | starts with `-` and the next positional slot takes it | a positional, when the slot has `hyphen()` and the token is not an option in scope, or the slot is `as_f32`, the token is a negative number and no short in scope is a digit |
| R4 | `-` followed by characters | a short cluster: each character must be a short in scope (else E01 quoting `-c`). Flags record and continue. An option takes the rest of the token (minus one leading `=`) if not empty, else the next token (R6), and ends the cluster. |
| R5 | anything else, including `-` and `""` | on a command with subcommands: descend into the named subcommand; with `external()`, keep this and every later token and stop; otherwise E02. On a command without: a positional (E09 when no slot is left). The first value of a `rest()` slot starts R0. |
| R6 | an option needs the next token | it is the value if it exists, is not `--`, and either does not start with `-`, is `-`, the option has `hyphen()`, or the option is `as_f32`, the token is a negative number and no short in scope is a digit. Otherwise E03. |

- A **negative number** is `-` followed by text in the `as_f32` grammar.
- Values convert as they are recorded; a failure is E04.
- A single-valued option keeps its last occurrence; lists keep all, in order.
  `delim` splits each value first, and each element converts on its own.
- Occurrences of a global merge under one id, whatever command they appear
  in.
- After an error, scanning continues so that a later `-h` or `--version` is
  still found. E02 and `external()` stop the scan.

## Positionals

The slots are the declared positionals in order, with at most one variadic.
With k positional tokens, the variadic slot at position v and r single slots
after it:

- each slot before v takes one token;
- slot v takes max(0, k − (v − 1) − r) tokens;
- each slot after v takes one token.

So `cp <SRC>... <DEST>` fills `DEST` before `SRC`.

## Subcommands

- A command with subcommands has no positionals. Options before the
  subcommand name belong to that command.
- After descending, the parent's non-global options are out of scope (E01,
  with tip T1).
- A missing subcommand completes the command when it has `sub_optional()`;
  otherwise it is E10, or summary help when argv is empty.
- `help [COMMAND]...` prints the full help for that path. An unknown name is
  E02 with suggestions.
- Paths that can run: commands without subcommands, and commands with
  `sub_optional()` or `external()`.

## Sources

Precedence: argv, then the environment (set and not empty), then the
default. Flags and switches read the environment as `as_bool`; counts as
`as_nat`; valued arguments by their type, split on `delim`. A bad environment
value is E11.

Defaults neither trigger nor satisfy `conflicts`, `requires` or groups. Only
argv or the environment satisfies `required()`.

## Outcome

After the scan, the first rule that applies decides:

| # | Rule | Outcome |
|---|---|---|
| V1 | `-h` or `--help` was scanned (the first of help and version wins) | help for that command: summary for `-h`, full for `--help`; stdout; exit 0 |
| V2 | `-V` or `--version` was scanned | `<name> <version>`; stdout; exit 0 |
| V3 | argv is empty and the root is missing a subcommand or a required argument | summary help; stderr; exit 2 |
| V4 | a scan error | that error; exit 2 |
| V5 | a check below fails | the first failure; exit 2 |
| V6 | `completions` or `man` was selected | the script or page; stdout; exit 0 |
| V7 | decode | `Go{value, term}`; `Cli.fail` is E12 (exit 2); `Cli.bug` exits 70 |

Checks, in order:

| # | Check | Error |
|---|---|---|
| C1 | a required subcommand was given | E10 |
| C2 | environment and default values convert | E11 |
| C3 | every required option, required positional and `need_one` group has a value | E06, listing every missing item |
| C4 | no `conflicts` or `exclusive` pair is present | E07, first pair |
| C5 | every `requires` is met | E08, first pair |

C4 and C5 consider arguments from argv in order of first occurrence, then
arguments from the environment in declaration order.

## Determinism

`eval` depends only on the definition, the host and argv. Its output is
byte-identical in native builds, compiled JavaScript and `bend main.bend`.
