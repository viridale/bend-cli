# Readers

Readers take `(m: Cli.Matches, id: String)` and return `Cli.Dec(T)`. Use them
in a `do Cli.Dec<A>:` block.

## Which reader

| Argument | Value type | Reader | T |
|---|---|---|---|
| flag, `--[no-]` switch | — | `flag` | `Bool` |
| count (`...` flag) | — | `count` | `Nat` |
| single value that always has one¹ | string, `as_file`, `as_dir`, `one_of` | `str` | `String` |
| | `as_nat` | `nat` | `Nat` |
| | `as_u32` | `u32` | `U32` |
| | `as_f32` | `f32` | `F32` |
| | `as_bool` | `bool` | `Bool` |
| single value that may be absent | each type above | `str_opt`, `nat_opt`, `u32_opt`, `f32_opt`, `bool_opt` | `Maybe<&2, T>` |
| list option, variadic positional | each type above | `strs`, `nats`, `u32s`, `f32s`, `bools` | `List<&2, T>` |
| any | — | `given` | `Bool`: present from argv or the environment |
| any | — | `source` | `Src`: `Argv{}`, `Env{}`, `Default{}` or `Absent{}` |

¹ It has `required()`, a default, or is a required positional (`<P>`). The
`_opt` readers also work on these.

## Choices

```python
choose(-A: Data, m, id, table: List<(String & A)>) -> Dec(A)
choose_opt(-A: Data, m, id, table: List<(String & A)>) -> Dec(Maybe<&2, A>)
```

For a `one_of` argument: returns the table value whose key equals the
argument's value. The keys must be exactly the `one_of` values. `choose` fits
an argument that always has a value; `choose_opt` gives `None{}` when it is
absent.

## Commands

```python
path(m) -> List<&2, String>                       # e.g. ["remote", "add"]
route(-A: Type, m, table: List<(String & (@+m: Matches -> Dec(A)))>) -> Dec(A)
external_args(m) -> Maybe<(String & List<&2, String>)>
```

`route` keys are command paths joined with one space (`"remote add"`); the
root is `""`. Aliases are not keys. `route` returns the selected callback's
result unchanged.

## Results

```python
Dec.pure(-A: Type, x: A) -> Dec(A)       # what `return` uses
fail(-A: Type, msg: String) -> Dec(A)    # usage error, exit 2
bug(-A: Type, msg: String) -> Dec(A)     # program bug, exit 70
keep(+m: Matches) -> Dec(Matches)        # the identity decoder
```

## Validation

Readers, `choose` and `route` check their arguments against the definition
before reading. A failed check is a `bug` (exit 70) with one of these
messages, and `Cli.check` reports it as a `DecodeBug`:

| Mistake | Message |
|---|---|
| the id is not in scope at this command | `'<id>' is not an argument of '<path>'` |
| the reader does not fit the argument | `'<id>' is <kind>; read it with Cli.<reader>` |
| a bare reader or `choose` on an argument that may be absent | `'<id>' may be absent; read it with Cli.<reader>_opt` |
| `choose` keys differ from the `one_of` values | `choose table for '<id>' does not match its values` |
| `route` has no key for this path | `no route for '<path>'` |
| a `route` key names no command, or a built-in | `route '<key>' is not a command` |

`<path>` starts with the root name: `'pkg add'`. These checks depend only on
the definition, never on argv, so if `Cli.check` passes they never fire.
When a key repeats in a `choose` or `route` table, the first entry wins.

## Other helpers

```python
suggest(input: String, names: List<&2, String>) -> List<&2, String>
```

The library's own did-you-mean rule, for use in your own errors: up to 3
names within edit distance `max(1, ⌊len/3⌋)`, nearest first.
