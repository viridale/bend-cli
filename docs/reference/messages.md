# Messages

Every message the library prints, with its exact text. Placeholders are in
angle brackets.

## Exit codes

| Code | Meaning | Stream |
|---|---|---|
| 0 | help, version, completions, man; or `act` returned 0 | stdout |
| 1–255 | returned by `act` (1: failure, by convention) | the app's choice |
| 2 | usage error, including `Cli.fail` and help shown for an empty command line | stderr |
| 70 | definition problems, `Cli.bug`, or `act` returning more than 255 | stderr |

Every non-empty output ends with exactly one newline. Library output never
writes to both streams.

## Usage errors

```
error: <message>

  tip: <tip>

Usage: <usage of the command where the error occurred>

For more information, try '--help'.
```

The tip block has zero or more lines and is omitted when empty. `<arg>` is
the argument's usage string without its short name when it also has a long
one (`--times <N>`, `-o <FILE>`, `<SRC>...`).

| Id | Message | When |
|---|---|---|
| E01 | `unexpected argument '<token>' found` | an unknown option; for a short cluster, the first unknown `-c` |
| E02 | `unrecognized subcommand '<name>'` | a token that names no subcommand where one is expected |
| E03 | `a value is required for '<arg>' but none was supplied` | an option at the end of argv, or followed by something that looks like an option or `--` |
| E04 | `invalid value '<value>' for '<arg>': <reason>` | a value that does not convert ([reasons](#value-reasons)) |
| E05 | `unexpected value '<value>' for '<arg>' found; no more were expected` | `--flag=value` on a flag, count or switch |
| E06 | `the following required arguments were not provided:` then one line per item, `  <arg>` or `  <--a\|--b>` | missing required options, positionals and `need_one` groups, all listed |
| E07 | `the argument '<a>' cannot be used with '<b>'` | a `conflicts` or `exclusive` pair; `a` is the one given later |
| E08 | `the argument '<a>' requires '<b>'` | an unmet `requires` |
| E09 | `unexpected argument '<token>' found` | a positional with no slot left |
| E10 | `'<path>' requires a subcommand but none was provided` then `  [subcommands: a, b]` | a required subcommand is missing (below the root) |
| E11 | `invalid value '<value>' for '<arg>' from environment variable <NAME>: <reason>` | an environment value that does not convert |
| E12 | `<msg>` | `Cli.fail(A, msg)` from the decoder |

When several problems occur, the first one found while scanning is reported.
`-h`, `--help`, `-V` and `--version` win over most errors: `app --bogus -h`
prints help.

### Value reasons

| Type | Reason |
|---|---|
| `as_nat` | `expected a whole number from 0 to 281474976710655` |
| `as_u32` | `expected a whole number from 0 to 4294967295` |
| `as_f32` | `expected a decimal number` |
| `as_bool` | `expected true or false` |
| `one_of` | `expected one of 'a', 'b', 'c'` |

## Tips

Every tip that applies is shown, in this order:

| Id | When | Text |
|---|---|---|
| T1 | E01 on an option of an ancestor command that is not global | `'<token>' belongs to '<owner path>'; place it before '<child>'` |
| T2 | E01 on an option that exists in a subcommand | `'<token>' belongs to subcommand '<path>'` |
| T3 | E01 on `--<name>` where `name` is a subcommand | `subcommand '<name>' exists; to use it, remove the '--'` |
| T4 | E01, E02, or E04 on `one_of`, with suggestions | `a similar <argument\|subcommand\|value> exists: '<x>'`, or `some similar <kind>s exist: '<x>', '<y>'` |
| T5 | E01 or E09 on a token starting with `-` that a positional could take | `to pass '<token>' as a value, use '-- <token>'` |

### Suggestions

- Candidates: for E01, the visible long names in scope, with aliases and
  `--no-` forms; for E02, subcommand names and aliases; for E04, the `one_of`
  values.
- Distance: optimal string alignment over code points (insert, delete,
  substitute, swap two neighbors), both sides cut to 64 characters.
- A candidate qualifies at distance ≤ max(1, ⌊n/3⌋), where n is the length
  of what the user typed, without dashes. So 1 edit up to 5 characters, 2
  edits from 6, 3 from 9.
- At most 3 are shown, nearest first, then in declaration order.

## Bugs (exit 70)

| Cause | stderr |
|---|---|
| definition problems | `bug: invalid command-line definition`, then one line per problem: `  <at>: <sentence>` |
| `Cli.bug(A, msg)`, or a reader validation failure | `bug: <msg>` |
| `act` returned more than 255 | `bug: exit code <n> is out of range 0..255` |

Reader validation messages are listed in [Readers](readers.md#validation).

## Definition problems

`Cli.problems(c)` and `Cli.check` return these, in pre-order: each command,
then its items in declaration order. `at` is the command path starting with
the root name (`"pkg add"`).

```python
type Problem is Data:
  BadUsage{at: String, usage: String, col: Nat}
  BadName{at: String, name: String}
  Dup{at: String, name: String}
  Reserved{at: String, name: String}
  Misplaced{at: String, attr: String}
  NoHelp{at: String, what: String}
  BadDefault{at: String, id: String, value: String}
  BadRef{at: String, id: String}
  BadPositional{at: String, id: String, why: String}
  Mixed{at: String}
  BadChoices{at: String, id: String}
  NeedBare{at: String, id: String}
  DecodeBug{at: String, msg: String}
```

| Problem | Raised when | Fix |
|---|---|---|
| `BadUsage` | a usage string breaks the [grammar](usage-strings.md#grammar); `col` is the first bad character | correct the string |
| `BadName` | a command or alias name is not a valid NAME, or an argument alias is malformed | letters, digits, `-`, `_`, `.` |
| `Dup` | a long, short, id or subcommand name repeats in one scope (globals included) | rename one, or use `id` |
| `Reserved` | `--help`; `--version` with `version` set; a subcommand named `help` where there are subcommands | rename |
| `Misplaced` | an attribute outside its [positions](attributes.md); a second value type; an argument or subcommand inside an argument | move or remove it |
| `NoHelp` | a visible command or argument with empty help | write help, or hide it |
| `BadDefault` | a default that does not convert (with `delim`, the first bad element); `required()` with `default` | correct the default |
| `BadRef` | `conflicts`/`requires` naming no id in scope; `exclusive`/`need_one` naming an empty group; a group no rule uses | correct the id or group |
| `BadPositional` | slot order breaks the rules; `why` says which | reorder the positionals |
| `Mixed` | a command with both positionals and subcommands | split the command |
| `BadChoices` | `one_of` empty or with duplicates | correct the list |
| `NeedBare` | `[=<V>]` without `bare`; `bare` elsewhere; a short name on an `[=<V>]` option | add `bare` or change the form |
| `DecodeBug` | only from `check`: the decoder raised `Cli.bug` on a sample | fix the decoder |

`BadPositional.why` is one of:

- `required positional follows an optional positional`
- `more than one variadic positional`
- `optional positional follows a variadic positional`
- `rest must be on the last positional`

Fields keep the declaration's spelling: `usage` is the full usage string,
`name` keeps its dashes, `attr` is the bare builder name (`global`).
