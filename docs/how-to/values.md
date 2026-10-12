# Typed and restricted values

Values are strings unless you give the argument a value type. A typed value
is checked while parsing, so a bad value is a usage error that names the
argument, and your decoder only ever sees valid values.

| Attribute | Accepts | Readers | Error reason |
|---|---|---|---|
| (none) | any text, including empty | `str`, `str_opt`, `strs` | — |
| `Cli.as_file()`, `Cli.as_dir()` | any text; completes file or directory names | `str`, `str_opt`, `strs` | — |
| `Cli.as_nat()` | `0` to `281474976710655` | `nat`, `nat_opt`, `nats` | `expected a whole number from 0 to 281474976710655` |
| `Cli.as_u32()` | `0` to `4294967295` | `u32`, `u32_opt`, `u32s` | `expected a whole number from 0 to 4294967295` |
| `Cli.as_f32()` | `1`, `-2.5`, `.5`, `3.`, `1e-3` | `f32`, `f32_opt`, `f32s` | `expected a decimal number` |
| `Cli.as_bool()` | `true false yes no on off 1 0`, any case | `bool`, `bool_opt`, `bools` | `expected true or false` |
| `Cli.one_of([...])` | exactly one of the listed strings | `str`…, `choose`, `choose_opt` | `expected one of 'a', 'b', 'c'` |

An argument has at most one value type. Whole numbers are digits only: no
sign, no `_`, no hex. Decimals do not accept `nan`, `inf`, `+3` or spaces.

```console
$ app --jobs -1
error: a value is required for '--jobs <N>' but none was supplied
$ app --jobs 1e3
error: invalid value '1e3' for '--jobs <N>': expected a whole number from 0 to 4294967295
```

`as_file` and `as_dir` do not check that the path exists; that is a fact
about the file system at run time, so check it in `act` where you open the
file, and report failure there.

## Choices mapped to your own type

`one_of` restricts the text. `choose` maps it to a value of your type:

```python
type Format is Data:
  Text{}
  Json{}

Cli.arg("--format <FMT>", "Output format",
  [Cli.one_of(["text", "json"]), Cli.default("text")])

format : Format <- Cli.choose(Format, m, "format", [("text", Text{}), ("json", Json{})])
```

For an argument that may be absent, use `Cli.choose_opt`, which gives a
`Maybe`. The table must have exactly the `one_of` values as keys; `Cli.check`
reports a table that misses or adds one, so adding a value to `one_of`
without handling it is caught by your `cli_ok` law.

Help lists the values (`[possible values: text, json]`), completions offer
them, and a near miss gets a suggestion:

```console
$ app --format jsn
error: invalid value 'jsn' for '--format <FMT>': expected one of 'text', 'json'

  tip: a similar value exists: 'json'
```

Matching is case-sensitive.

## Validation the parser cannot express

Anything else goes in the decoder. `Cli.fail(T, msg)` is a usage error (exit
2) with your message in the standard error shape:

```python
def port_ok(low: Bool, port: U32) -> Cli.Dec(U32):
  match low:
    case True{}:
      Cli.fail(U32, "--port must be 1024 or above; lower ports need root")
    case False{}:
      Cli.Dec.pure(U32, port)

def check_port(+port: U32) -> Cli.Dec(U32):
  port_ok(U32.is_lt(port, 1024), port)
```

```python
    raw : U32 <- Cli.u32(m, "port")
    port : U32 <- check_port(raw)
```

```console
$ app --port 80
error: --port must be 1024 or above; lower ports need root

Usage: app [OPTIONS]

For more information, try '--help'.
```

Write the message as a full sentence about the argument, as the parser's own
messages do. Read every argument first and validate afterwards, so that
[`Cli.check`](testing.md#the-definition-check) can exercise every read.

## Parsing your own formats

For a value with structure, such as a duration `10s` or a pair `KEY=VALUE`,
read it as a string and parse it in the decoder:

```python
def pair(found: Maybe<(String & String)>, text: String) -> Cli.Dec((String & String)):
  match found:
    case Some{kv}:
      Cli.Dec.pure((String & String), kv)
    case None{}:
      Cli.fail((String & String),
        ("--set expects KEY=VALUE, got '" ++ text ++ "'" : String))
```

where `found` comes from your own splitting function. For a repeated option,
walk the list from `Cli.strs` and fail on the first bad element.

## Floating point

`Cli.f32` gives an `F32`. `-5` is a value, not an option, for an `as_f32`
argument unless a short option in scope is a digit (`-1`). Bend's checker does
not evaluate `F32.read`, so a law about a parsed decimal cannot be proved by
`{==}`; test those with end-to-end cases instead.

See also: [Readers](../reference/readers.md), [Errors and exit
codes](errors.md).
