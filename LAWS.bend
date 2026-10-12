# Purpose: laws for the pure CLI library and pkg demo.
# Expected output: ALL PROOFS CHECK.
# Run: bend PROOF.bend --verdict
# Scope: P13 bounds visible line widths; P14 preserves words in order. Neither
# pins whitespace normalization; G-TEXT pins representative wrapped content.
# P12 fixes when readers, choose and route raise their own validation Bug,
# not what they return; G-READ fixes values, except a given f32 (K8), and
# what route's selected callback returns. P7 and P8 fix term's colors;
# G-HELP, G-ERR, G-TIP and G-COLOR fix outcome's bytes for V1-V5, not what
# outcome's Matched holds, nor completions, man or decoding (M5, M6).

import Base
import ./cli.bend as Cli
import ./demo.bend as Demo

# Segment is the internal styled-text value used by emit: text, then styles.

# P1: disabled painting is identity; stripping preserves ESC-free source text.
law p1:
  for on: Bool
  for +styles: List<&2, Cli.Style>
  for +s: String
  {Cli.paint(False{}, styles, s) == s : String} &
  ({String.contains(s, "\u{1B}") == False{} : Bool} ->
   {Cli.strip(Cli.paint(on, styles, s)) == s : String})

# P2: stripping emitted styles preserves ESC-free segment text.
law p2:
  for +segments: List<&2, Cli.Segment>
  {String.contains(Cli.emit(False{}, segments), "\u{1B}") == False{} : Bool} ->
  {Cli.strip(Cli.emit(True{}, segments))
    == Cli.emit(False{}, segments) : String}

# P13: each wrapped line fits visibly, or has at most one space-delimited word.
def p13_good(+cols: Nat, lines: List<&2, String>) -> Bool:
  match lines:
    case Nil{}: True{}
    case +line <> tail:
      Bool.and(Bool.or(Nat.is_le(Cli.width(Cli.strip(line)), cols),
        Nat.is_le(List.length(&2, String, Cli.words(line)), 1n)),
        p13_good(cols, tail))

law p13:
  for s: String
  for +cols: Nat
  {p13_good(cols, String.lines(Cli.wrap(s, cols))) == True{} : Bool}

# P14: wrapping preserves every space-delimited word in its original order.
def all_words(lines: List<&2, String>) -> List<&2, String>:
  match lines:
    case Nil{}: Nil{}
    case line <> tail:
      List.append(&2, String, Cli.words(line), all_words(tail))

law p14:
  for +s: String
  for cols: Nat
  {all_words(String.lines(Cli.wrap(s, cols)))
    == all_words(String.lines(s)) : List<&2, String>}

# G-TEXT: U+31EF changes from width 1 to 2 in Unicode 15.1.
law g_text_width:
  {Cli.width("abc") == 3n : Nat} &
  {Cli.width("界") == 2n : Nat} &
  {Cli.width("\u{31EF}") == 2n : Nat} &
  {Cli.width("e\u{301}") == 1n : Nat} &
  {Cli.width("\u{1B}") == 0n : Nat}

# G-TEXT: wrapping is greedy, normalizes spaces, and keeps long words whole.
law g_text_wrap:
  {Cli.wrap("alpha beta gamma", 10n) == "alpha beta\ngamma" : String} &
  {Cli.wrap("abc defg h", 6n) == "abc\ndefg h" : String} &
  {Cli.wrap("  alpha beta", 8n) == "  alpha\n  beta" : String} &
  {Cli.wrap("a elephant b", 4n) == "a\nelephant\nb" : String} &
  {Cli.wrap("a  b", 80n) == "a b" : String} &
  {Cli.wrap("x\n   \ny", 80n) == "x\n\ny" : String}

# G-TEXT: styles reset after a span; an empty style list paints no bytes.
law g_text_paint:
  {Cli.paint(True{}, [Cli.Bold{}, Cli.Red{}], "x")
    == "\u{1B}[1;31mx\u{1B}[0m" : String} &
  {Cli.paint(True{}, [], "x") == "x" : String}

# G-TEXT: strip removes SGR grammar matches and preserves an unmatched ESC.
law g_text_strip:
  {Cli.strip("\u{1B}[0m\u{1B}[ma\u{1B}[1;31mb\u{1B}[Xm")
    == "ab\u{1B}[Xm" : String}

# G-TEXT: emit joins segments in order and styles only nonempty style lists.
law g_text_emit:
  {Cli.emit(False{}, [
    Cli.Segment{"one", [Cli.Bold{}]},
    Cli.Segment{"two", []},
  ]) == "onetwo" : String} &
  {Cli.emit(True{}, [
    Cli.Segment{"one", [Cli.Bold{}]},
    Cli.Segment{"two", []},
  ]) == "\u{1B}[1mone\u{1B}[0mtwo" : String}

# G-USAGE: every declared form in section 6.3 is accepted by the parser.
law g_usage_forms:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("-h", "Human-readable sizes", []),
    Cli.arg("-b, --brief", "Brief output", []),
    Cli.arg("--trace", "Trace output", []),
    Cli.arg("-q, --quiet...", "Reduce output", []),
    Cli.arg("-s, --[no-]safe", "Enable safety", []),
    Cli.arg("--[no-]x", "Enable x", []),
    Cli.arg("-C <DIR>", "Working directory", []),
    Cli.arg("-o, --output <FILE>", "Output file", []),
    Cli.arg("--include <PATH>...", "Include paths", []),
    Cli.arg("--color[=<WHEN>]", "Color mode", [Cli.bare("auto")]),
    Cli.arg("<SRC>", "Source", []),
    Cli.arg("[DEST]", "Destination", []),
    Cli.arg("[EXTRA]...", "Extra inputs", []),
  ])) == [] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("<P>...", "Inputs", []),
  ])) == [] : List<&2, Cli.Problem>}

# G-LINT: a well-formed command has no problems.
law g_lint_valid:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--quiet", "Quiet output", []),
    Cli.arg("--mode <MODE>", "Output mode",
      [Cli.one_of(["text", "json"]), Cli.default("text")]),
    Cli.arg("[FILE]", "Input file", []),
  ])) == [] : List<&2, Cli.Problem>}

# G-LINT BadUsage: col is the zero-based index of the first bad character.
law g_lint_bad_usage:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--bad?", "Bad option", []),
  ])) == [Cli.BadUsage{"tool", "--bad?", 5n}]
    : List<&2, Cli.Problem>}

# G-LINT BadUsage: the first trailing dot is the bad column, even before repeat.
law g_lint_bad_usage_trailing_dot:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--quiet.", "Bad option", []),
  ])) == [Cli.BadUsage{"tool", "--quiet.", 7n}]
    : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--quiet....", "Bad count", []),
  ])) == [Cli.BadUsage{"tool", "--quiet....", 7n}]
    : List<&2, Cli.Problem>}

# G-LINT BadName: a subcommand name must follow NAME.
law g_lint_bad_name:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.sub("bad name", "Bad subcommand", []),
  ])) == [Cli.BadName{"tool", "bad name"}]
    : List<&2, Cli.Problem>}

# G-LINT Dup: two option names in one scope cannot coincide.
law g_lint_dup:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--flag", "First flag", [Cli.id("first")]),
    Cli.arg("--flag", "Second flag", [Cli.id("second")]),
  ])) == [Cli.Dup{"tool", "--flag"}]
    : List<&2, Cli.Problem>}

# G-LINT Dup: repeat suffix is syntax, not part of the option name.
law g_lint_dup_repeat:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--quiet", "Quiet flag", []),
    Cli.arg("--quiet...", "Quiet count", []),
  ])) == [Cli.Dup{"tool", "--quiet"}]
    : List<&2, Cli.Problem>}

# G-LINT Dup: an option and a positional cannot derive the same id.
law g_lint_dup_id:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--file <FILE>", "File option", []),
    Cli.arg("<FILE>", "File operand", []),
  ])) == [Cli.Dup{"tool", "file"}]
    : List<&2, Cli.Problem>}

# G-LINT: descendant options cannot shadow an ancestor global option.
law g_lint_dup_global:
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.arg("-v, --verbose", "Verbose", [Cli.global()]),
    Cli.sub("run", "Run", [Cli.arg("-v, --verify", "Verify", [])]),
  ])) == [Cli.Dup{"tool run", "-v"}] : List<&2, Cli.Problem>}

# G-LINT Dup: a repeated subcommand name is reported at the parent path.
law g_lint_dup_sub:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.sub("run", "First run command", []),
    Cli.sub("run", "Second run command", []),
  ])) == [Cli.Dup{"tool", "run"}]
    : List<&2, Cli.Problem>}

# G-LINT Reserved: --help belongs to the built-in help option.
law g_lint_reserved:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--help", "User option", []),
  ])) == [Cli.Reserved{"tool", "--help"}]
    : List<&2, Cli.Problem>}

# G-LINT Reserved: the built-in help subcommand owns its name.
law g_lint_reserved_sub:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.sub("help", "User help command", []),
  ])) == [Cli.Reserved{"tool", "help"}]
    : List<&2, Cli.Problem>}

# G-LINT Misplaced: global applies only to a non-positional argument.
law g_lint_misplaced:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("[FILE]", "Input file", [Cli.global()]),
  ])) == [Cli.Misplaced{"tool", "global"}]
    : List<&2, Cli.Problem>}

# G-LINT NoHelp: what keeps the full usage string as written.
law g_lint_no_help:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("-o, --output <FILE>", "", []),
  ])) == [Cli.NoHelp{"tool", "-o, --output <FILE>"}]
    : List<&2, Cli.Problem>}

# G-LINT NoHelp: a subcommand's missing about is reported at its own path.
law g_lint_no_help_sub:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.sub("run", "", []),
  ])) == [Cli.NoHelp{"tool run", "run"}]
    : List<&2, Cli.Problem>}

# G-LINT BadDefault: defaults must pass their declared value type.
law g_lint_bad_default:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--count <N>", "Count",
      [Cli.as_u32(), Cli.default("nope")]),
  ])) == [Cli.BadDefault{"tool", "count", "nope"}]
    : List<&2, Cli.Problem>}

# G-LINT BadRef: a requires target must name an id in scope.
law g_lint_bad_ref:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--flag", "Flag", [Cli.requires("missing")]),
  ])) == [Cli.BadRef{"tool", "missing"}]
    : List<&2, Cli.Problem>}

# G-LINT BadPositional: a required slot cannot follow an optional slot.
law g_lint_bad_positional:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("[A]", "Optional input", []),
    Cli.arg("<B>", "Required input", []),
  ])) == [Cli.BadPositional{
    "tool", "b", "required positional follows an optional positional"}]
    : List<&2, Cli.Problem>}

# G-LINT BadPositional: a second variadic is reported at the second slot.
law g_lint_bad_positional_two_variadics:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("<A>...", "First inputs", []),
    Cli.arg("<B>...", "Second inputs", []),
  ])) == [Cli.BadPositional{
    "tool", "b", "more than one variadic positional"}]
    : List<&2, Cli.Problem>}

# G-LINT BadPositional: an optional slot cannot follow a variadic slot.
law g_lint_bad_positional_optional_after_variadic:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("<A>...", "Inputs", []),
    Cli.arg("[B]", "Optional output", []),
  ])) == [Cli.BadPositional{
    "tool", "b", "optional positional follows a variadic positional"}]
    : List<&2, Cli.Problem>}

# G-LINT BadPositional: rest belongs only on the last positional.
law g_lint_bad_positional_rest:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("<A>...", "Inputs", [Cli.rest()]),
    Cli.arg("<B>", "Output", []),
  ])) == [Cli.BadPositional{
    "tool", "a", "rest must be on the last positional"}]
    : List<&2, Cli.Problem>}

# G-LINT Mixed: a command cannot have positionals and subcommands.
law g_lint_mixed:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("<FILE>", "Input file", []),
    Cli.sub("run", "Run command", []),
  ])) == [Cli.Mixed{"tool"}]
    : List<&2, Cli.Problem>}

# G-LINT BadChoices: a one_of set must be nonempty.
law g_lint_bad_choices:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--mode <MODE>", "Output mode", [Cli.one_of([])]),
  ])) == [Cli.BadChoices{"tool", "mode"}]
    : List<&2, Cli.Problem>}

# G-LINT NeedBare: an optional-value option requires a bare value.
law g_lint_need_bare:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--color[=<WHEN>]", "Color mode", []),
  ])) == [Cli.NeedBare{"tool", "color"}]
    : List<&2, Cli.Problem>}


def same_strings(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs ys:
    case Nil{} Nil{}: True{}
    case Nil{} head <> tail: False{}
    case head <> tail Nil{}: False{}
    case x <> xt y <> yt:
      Bool.and(String.eq(x, y), same_strings(xt, yt))

def has_suffix(+post: List<&2, String>, all: List<&2, String>) -> Bool:
  same_strings(List.reverse(&2, String, post),
    List.take(&2, String, List.reverse(&2, String, all),
      List.length(&2, String, post)))

def operands(events: List<&2, Cli.ScanEvent>) -> List<&2, String>:
  match events:
    case Nil{}: Nil{}
    case Cli.Operand{token} <> tail: token <> operands(tail)
    case event <> tail: operands(tail)

def p9_trace(pre: List<&2, String>, post: List<&2, String>,
    trace: Cli.ScanTrace) -> Bool:
  match trace:
    case Cli.ScanTrace{path, events, ended, external, issue}:
      premise = Bool.and(
        Bool.not(List.contains(~String, ~String.eq, pre, "--")),
        Bool.and(ended, Maybe.is_none(&2, Cli.ScanFault, issue)))
      Bool.or(Bool.not(premise), has_suffix(post, operands(events)))

def p9_holds(c: Cli.Cmd, +pre: List<&2, String>,
    +post: List<&2, String>) -> Bool:
  p9_trace(pre, post,
    Cli.scan(c, List.append(&2, String, pre, "--" <> post)))

# P9: after a reached `--`, each later token remains a positional token.
# `ended` excludes a scan stopped before `--` (E02, external()) and a `--`
# taken as a value by rest().
law p9:
  for c: Cli.Cmd
  for +pre: List<&2, String>
  for +post: List<&2, String>
  {p9_holds(c, pre, post) == True{} : Bool}

def root(events: List<&2, Cli.ScanEvent>,
    ended: Bool,
    issue: Maybe<&2, Cli.ScanFault>) -> Cli.ScanTrace:
  Cli.ScanTrace{[], events, ended, None{}, issue}

def flags() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-a", "Flag a", []),
    Cli.arg("-b", "Flag b", []),
    Cli.arg("-c", "Flag c", []),
  ])

# G-LEX: a short cluster is scanned left to right.
law g_lex_cluster:
  {Cli.scan(flags(), ["-abc"]) == root([
    Cli.FlagHit{"a", True{}},
    Cli.FlagHit{"b", True{}},
    Cli.FlagHit{"c", True{}},
  ], False{}, None{}) : Cli.ScanTrace}

def out_option() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-o, --out <FILE>", "Output", []),
  ])

# G-LEX: attached, separated, long, and empty option values.
law g_lex_values:
  {Cli.scan(out_option(), ["-ofile"]) == root([
    Cli.ValueHit{"out", "file"},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(out_option(), ["-o=file"]) == root([
    Cli.ValueHit{"out", "file"},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(out_option(), ["-o", "file"]) == root([
    Cli.ValueHit{"out", "file"},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(out_option(), ["--out=file"]) == root([
    Cli.ValueHit{"out", "file"},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(out_option(), ["--out", "file"]) == root([
    Cli.ValueHit{"out", "file"},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(out_option(), ["--out="]) == root([
    Cli.ValueHit{"out", ""},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(out_option(), ["-o"]) == root(
    [], False{}, Some{Cli.E03{"--out <FILE>"}}) : Cli.ScanTrace}

def optional_operand() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("[X]", "Operand", []),
  ])

# G-LEX: a lone hyphen is an operand; `--` ends option lookup.
law g_lex_end:
  {Cli.scan(optional_operand(), ["-"]) == root([
    Cli.Operand{"-"},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(optional_operand(), ["--", "-x"]) == root([
    Cli.Operand{"-x"},
  ], True{}, None{}) : Cli.ScanTrace}

def host() -> Cli.Host:
  Cli.host(80n)

def ok(fields: List<&2, Cli.Field>) -> Cli.ParseResult:
  Cli.Accepted{[], fields, None{}}

def field(id: String, values: List<&2, String>,
    source: Cli.Src) -> Cli.Field:
  Cli.Field{id, values, source}

def count_option() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-v, --verbose...", "Verbosity", []),
  ])

# G-LEX: every short count occurrence contributes one, including clusters.
law g_lex_count:
  {Cli.scan(count_option(), ["-vvv"]) == root([
    Cli.CountHit{"verbose"}, Cli.CountHit{"verbose"},
    Cli.CountHit{"verbose"},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.parse(count_option(), host(), ["-vvv"]) == ok([
    field("verbose", ["3"], Cli.Argv{}),
  ]) : Cli.ParseResult}

def negatable_option() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--[no-]x", "Toggle x", []),
  ])

# G-LEX: negatable options record polarity; the last occurrence wins.
law g_lex_negation:
  {Cli.scan(negatable_option(), ["--no-x"]) == root([
    Cli.FlagHit{"x", False{}},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(negatable_option(), ["--x", "--no-x"]) == root([
    Cli.FlagHit{"x", True{}}, Cli.FlagHit{"x", False{}},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.parse(negatable_option(), host(), ["--x", "--no-x"]) == ok([
    field("x", ["false"], Cli.Argv{}),
  ]) : Cli.ParseResult}

def color_option() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--color[=<WHEN>]", "Color mode", [Cli.bare("auto")]),
  ])

# G-LEX: an optional-value option uses its bare value without `=`.
law g_lex_bare:
  {Cli.scan(color_option(), ["--color"]) == root([
    Cli.ValueHit{"color", "auto"},
  ], False{}, None{}) : Cli.ScanTrace}

def decimal_option(typed: Bool) -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-m <NUM>", "Decimal", Bool.pick(List<&2, Cli.Item>, typed,
      [Cli.as_f32()], [])),
  ])

# G-LEX: a negative value needs as_f32; a flag rejects `=value`.
law g_lex_errors:
  {Cli.scan(decimal_option(False{}), ["-m", "-5"]) == root(
    [], False{}, Some{Cli.E03{"-m <NUM>"}}) : Cli.ScanTrace} &
  {Cli.scan(decimal_option(True{}), ["-m", "-5"]) == root([
    Cli.ValueHit{"m", "-5"},
  ], False{}, None{}) : Cli.ScanTrace} &
  {Cli.scan(Cli.cmd("tool", "Tool", [
    Cli.arg("--flag", "Flag", []),
  ]), ["--flag=x"]) == root(
    [], False{}, Some{Cli.E05{"--flag", "x"}}) : Cli.ScanTrace} &
  {Cli.scan(Cli.cmd("tool", "Tool", [
    Cli.arg("-a", "Flag a", []),
  ]), ["-az"]) == root([
    Cli.FlagHit{"a", True{}},
  ], False{}, Some{Cli.E01{"-z"}}) : Cli.ScanTrace}

# G-LEX: recovery records a later help token while retaining the first error.
law g_lex_recovery:
  {Cli.scan(flags(), ["--bad=x", "--help"]) == root([
    Cli.HelpHit{True{}},
  ], False{}, Some{Cli.E01{"--bad"}}) : Cli.ScanTrace}

def cp() -> Cli.Cmd:
  Cli.cmd("cp", "Copy files", [
    Cli.arg("<SRC>...", "Sources", []),
    Cli.arg("<DST>", "Destination", []),
  ])

# G-POS: a variadic slot leaves one token for the required trailing slot.
law g_pos_variadic:
  {Cli.parse(cp(), host(), ["a", "b", "dest"]) == ok([
    field("src", ["a", "b"], Cli.Argv{}),
    field("dst", ["dest"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(cp(), host(), ["a", "dest"]) == ok([
    field("src", ["a"], Cli.Argv{}),
    field("dst", ["dest"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(cp(), host(), ["dest"]) ==
    Cli.Rejected{[], Cli.E06{["<SRC>..."]}} : Cli.ParseResult}

# G-POS: optional absence, excess input, rest, and hyphen slots.
law g_pos_cases:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("[OUT]", "Output", []),
  ]), host(), []) == ok([]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("<X>", "Operand", []),
  ]), host(), ["a", "b"]) ==
    Cli.Rejected{[], Cli.E09{"b"}} : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("<ITEM>...", "Items", [Cli.rest()]),
  ]), host(), ["a", "--", "-x"]) == ok([
    field("item", ["a", "--", "-x"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("<X>", "Operand", [Cli.hyphen()]),
  ]), host(), ["-x"]) == ok([
    field("x", ["-x"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("[X]", "Operand", []),
  ]), host(), [""]) == ok([
    field("x", [""], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("<N>", "Number", [Cli.as_f32()]),
  ]), host(), ["-5"]) == ok([
    field("n", ["-5"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("<N>", "Number", [Cli.as_nat()]),
  ]), host(), ["x"]) ==
    Cli.Rejected{[], Cli.E04{"<N>", "x",
      "expected a whole number from 0 to 281474976710655"}}
    : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("<X>", "Operand", [Cli.hyphen()]),
  ]), host(), ["-h"]) ==
    Cli.HelpRequested{[], False{}} : Cli.ParseResult}

def sub_tool() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--root", "Root only", []),
    Cli.arg("-g, --global", "Global flag", [Cli.global()]),
    Cli.sub("alpha", "Alpha", [
      Cli.alias("a"),
      Cli.sub_optional(),
      Cli.arg("--child", "Child flag", []),
      Cli.sub("beta", "Beta", []),
    ]),
  ])

# G-SUB: descent changes the scope; globals merge across the boundary.
law g_sub_descent:
  {Cli.scan(sub_tool(), ["-g", "alpha", "-g", "--child"]) ==
    Cli.ScanTrace{["alpha"], [
      Cli.FlagHit{"global", True{}}, Cli.Enter{"alpha"},
      Cli.FlagHit{"global", True{}}, Cli.FlagHit{"child", True{}},
    ], False{}, None{}, None{}} : Cli.ScanTrace} &
  {Cli.parse(sub_tool(), host(), ["-g", "alpha", "--child"]) ==
    Cli.Accepted{["alpha"], [
      field("global", ["true"], Cli.Argv{}),
      field("child", ["true"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult} &
  {Cli.parse(sub_tool(), host(), ["alpha", "-g"]) ==
    Cli.Accepted{["alpha"], [
      field("global", ["true"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult}

# G-SUB: an alias resolves to the declared path.
law g_sub_alias:
  {Cli.parse(sub_tool(), host(), ["a", "beta"]) ==
    Cli.Accepted{["alpha", "beta"], [], None{}} : Cli.ParseResult}

# G-SUB: the help subcommand walks named descendants.
law g_sub_help:
  {Cli.parse(sub_tool(), host(), ["help"]) ==
    Cli.HelpRequested{[], True{}} : Cli.ParseResult} &
  {Cli.parse(sub_tool(), host(), ["help", "a", "beta"]) ==
    Cli.HelpRequested{["alpha", "beta"], True{}} : Cli.ParseResult} &
  {Cli.parse(sub_tool(), host(), ["help", "bad"]) ==
    Cli.Rejected{[], Cli.E02{"bad"}} : Cli.ParseResult} &
  {Cli.parse(sub_tool(), host(), ["alpha", "--help"]) ==
    Cli.HelpRequested{["alpha"], True{}} : Cli.ParseResult}

# G-SUB: former, future, and misspelled subcommand options are errors.
# G-TIP pins the T1-T3 text.
law g_sub_scope_errors:
  {Cli.parse(sub_tool(), host(), ["alpha", "--root"]) ==
    Cli.Rejected{["alpha"], Cli.E01{"--root"}} : Cli.ParseResult} &
  {Cli.parse(sub_tool(), host(), ["--child", "alpha"]) ==
    Cli.Rejected{[], Cli.E01{"--child"}} : Cli.ParseResult} &
  {Cli.parse(sub_tool(), host(), ["--alpha"]) ==
    Cli.Rejected{[], Cli.E01{"--alpha"}} : Cli.ParseResult}

def external_tool() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [Cli.external(),
    Cli.sub("known", "Known", []),
  ])

# G-SUB: external captures the name and untouched suffix, then stops scanning.
law g_sub_external:
  {Cli.parse(external_tool(), host(), ["plug", "--x", "--help"]) ==
    Cli.Accepted{[], [], Some{Cli.ExternalArgs{"plug", ["--x", "--help"]}}}
    : Cli.ParseResult} &
  {Cli.parse(external_tool(), host(), ["known"]) ==
    Cli.Accepted{["known"], [], None{}} : Cli.ParseResult}

# G-SUB: required descent fails on nonempty argv; empty argv asks for summary help.
law g_sub_missing:
  {Cli.parse(sub_tool(), host(), ["-g"]) ==
    Cli.Rejected{[], Cli.E10{}} : Cli.ParseResult} &
  {Cli.parse(sub_tool(), host(), []) ==
    Cli.SummaryRequired{} : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [Cli.sub_optional(),
    Cli.sub("alpha", "Alpha", []),
  ]), host(), []) == ok([]) : Cli.ParseResult}

# G-SUB: a user short option shadows only the matching built-in short.
law g_sub_short_shadow:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("-h", "Human", []),
  ]), host(), ["-h"]) == ok([
    field("h", ["true"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("-h", "Human", []),
  ]), host(), ["--help"]) ==
    Cli.HelpRequested{[], True{}} : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.version("1.0"), Cli.arg("-V", "Verbose", []),
  ]), host(), ["-V"]) == ok([
    field("V", ["true"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.version("1.0"), Cli.arg("-V", "Verbose", []),
  ]), host(), ["--version"]) ==
    Cli.VersionRequested{} : Cli.ParseResult}

def typed(attrs: List<&2, Cli.Item>) -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--value <V>", "Value", attrs),
  ])

# G-VAL: string, file, and directory values accept empty text.
law g_val_strings:
  {Cli.parse(typed([]), host(), ["--value="]) == ok([
    field("value", [""], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_file()]), host(), ["--value="]) == ok([
    field("value", [""], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_dir()]), host(), ["--value="]) == ok([
    field("value", [""], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([]), host(), ["--value=a", "--value=b"]) == ok([
    field("value", ["b"], Cli.Argv{}),
  ]) : Cli.ParseResult}

# G-VAL: Nat includes 0 and 2^48-1 and rejects the next integer.
law g_val_nat:
  {Cli.parse(typed([Cli.as_nat()]), host(), ["--value=0"]) == ok([
    field("value", ["0"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_nat()]), host(),
    ["--value=281474976710655"]) == ok([
      field("value", ["281474976710655"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_nat()]), host(),
    ["--value=281474976710656"]) == Cli.Rejected{[],
      Cli.E04{"--value <V>", "281474976710656",
        "expected a whole number from 0 to 281474976710655"}}
    : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_nat()]), host(), ["--value=-1"]) ==
    Cli.Rejected{[], Cli.E04{"--value <V>", "-1",
      "expected a whole number from 0 to 281474976710655"}}
    : Cli.ParseResult}

# G-VAL: U32 includes its bounds and rejects overflow with the exact reason.
law g_val_u32:
  {Cli.parse(typed([Cli.as_u32()]), host(), ["--value=0"]) == ok([
    field("value", ["0"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_u32()]), host(), ["--value=4294967295"]) == ok([
    field("value", ["4294967295"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_u32()]), host(), ["--value=4294967296"]) ==
    Cli.Rejected{[], Cli.E04{"--value <V>", "4294967296",
      "expected a whole number from 0 to 4294967295"}}
    : Cli.ParseResult}

# G-VAL: F32 accepts signed decimals and exponents, and rejects bad grammar.
law g_val_f32:
  {Cli.parse(typed([Cli.as_f32()]), host(), ["--value=-5"]) == ok([
    field("value", ["-5"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_f32()]), host(), ["--value=.5"]) == ok([
    field("value", [".5"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_f32()]), host(), ["--value=1e+3"]) == ok([
    field("value", ["1e+3"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_f32()]), host(), ["--value=1e"]) ==
    Cli.Rejected{[], Cli.E04{"--value <V>", "1e",
      "expected a decimal number"}} : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_f32()]), host(), ["--value=+3"]) ==
    Cli.Rejected{[], Cli.E04{"--value <V>", "+3",
      "expected a decimal number"}} : Cli.ParseResult}

# G-VAL: Bool accepts case-insensitive vocabulary and rejects other text.
law g_val_bool:
  {Cli.parse(typed([Cli.as_bool()]), host(), ["--value=YeS"]) == ok([
    field("value", ["YeS"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_bool()]), host(), ["--value=0"]) == ok([
    field("value", ["0"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_bool()]), host(), ["--value=maybe"]) ==
    Cli.Rejected{[], Cli.E04{"--value <V>", "maybe",
      "expected true or false"}} : Cli.ParseResult}

# G-VAL: one_of is case-sensitive; the reason lists candidates in order.
law g_val_one_of:
  {Cli.parse(typed([Cli.one_of(["red", "blue"])]), host(),
    ["--value=red"]) == ok([
      field("value", ["red"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.one_of(["red", "blue"])]), host(),
    ["--value=Red"]) == Cli.Rejected{[],
      Cli.E04{"--value <V>", "Red", "expected one of 'red', 'blue'"}}
    : Cli.ParseResult}

# G-VAL: delim splits each list occurrence and each variadic token in order.
law g_val_delim:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--tag <TAG>...", "Tags", [Cli.delim(',')]),
  ]), host(), ["--tag=a,b", "--tag=c"]) == ok([
    field("tag", ["a", "b", "c"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("<TAG>...", "Tags", [Cli.delim(',')]),
  ]), host(), ["a,b", "c"]) == ok([
    field("tag", ["a", "b", "c"], Cli.Argv{}),
  ]) : Cli.ParseResult}

def numbers(attrs: List<&2, Cli.Item>) -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--n <N>...", "Numbers", attrs),
  ])

def number_operands(attrs: List<&2, Cli.Item>) -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("<N>...", "Numbers", attrs),
  ])

# G-VAL: delim splits before conversion, in argv, env and defaults; E04, E11
# and BadDefault quote the first element that fails.
law g_val_delim_typed:
  {Cli.parse(numbers([Cli.as_nat(), Cli.delim(',')]), host(),
    ["--n=1,2", "--n", "3"]) == ok([
      field("n", ["1", "2", "3"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(number_operands([Cli.as_u32(), Cli.delim(',')]), host(),
    ["1,2"]) == ok([
      field("n", ["1", "2"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(numbers([Cli.as_bool(), Cli.delim(','), Cli.env("N")]),
    Cli.host_var(host(), "N", "yes,0"), []) == ok([
      field("n", ["yes", "0"], Cli.Env{}),
    ]) : Cli.ParseResult} &
  {Cli.problems(numbers([Cli.one_of(["a", "b"]), Cli.delim(','),
    Cli.default("b,a")])) == [] : List<&2, Cli.Problem>} &
  {Cli.parse(numbers([Cli.one_of(["a", "b"]), Cli.delim(','),
    Cli.default("b,a")]), host(), []) == ok([
      field("n", ["b", "a"], Cli.Default{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(numbers([Cli.as_nat(), Cli.delim(',')]), host(),
    ["--n=1,x"]) == Cli.Rejected{[], Cli.E04{"--n <N>...", "x",
      "expected a whole number from 0 to 281474976710655"}}
    : Cli.ParseResult} &
  {Cli.parse(numbers([Cli.as_nat(), Cli.delim(','), Cli.env("N")]),
    Cli.host_var(host(), "N", "1,x"), []) ==
    Cli.Rejected{[], Cli.E11{"--n <N>...", "x", "N",
      "expected a whole number from 0 to 281474976710655"}}
    : Cli.ParseResult} &
  {Cli.parse(number_operands([Cli.as_u32(), Cli.delim(',')]), host(),
    ["1,x,y"]) == Cli.Rejected{[], Cli.E04{"<N>...", "x",
      "expected a whole number from 0 to 4294967295"}}
    : Cli.ParseResult} &
  {Cli.problems(numbers([Cli.as_nat(), Cli.delim(','),
    Cli.default("1,x,y")])) == [Cli.BadDefault{"tool", "n", "x"}]
    : List<&2, Cli.Problem>}

def sourced() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--flag", "Flag", [Cli.env("TOOL_FLAG")]),
    Cli.arg("--verbose...", "Verbosity", [Cli.env("TOOL_VERBOSE")]),
    Cli.arg("--value <V>", "Value", [
      Cli.env("TOOL_VALUE"), Cli.default("fallback")]),
  ])

# G-SRC: environment supplies flag, count, and valued args when argv is absent.
law g_src_env:
  {Cli.parse(sourced(),
    Cli.host_var(Cli.host_var(Cli.host_var(host(),
      "TOOL_FLAG", "ON"), "TOOL_VERBOSE", "3"), "TOOL_VALUE", "env"),
    []) == ok([
      field("flag", ["true"], Cli.Env{}),
      field("verbose", ["3"], Cli.Env{}),
      field("value", ["env"], Cli.Env{}),
    ]) : Cli.ParseResult}

# G-SRC: an empty env value is unset, so the default supplies the value.
law g_src_empty_default:
  {Cli.parse(sourced(), Cli.host_var(host(), "TOOL_VALUE", ""), []) ==
    ok([field("value", ["fallback"], Cli.Default{})]) : Cli.ParseResult}

# G-SRC: argv wins over env; env wins over default.
law g_src_precedence:
  {Cli.parse(sourced(), Cli.host_var(host(), "TOOL_VALUE", "env"),
    ["--value=argv"]) == ok([
      field("value", ["argv"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(sourced(), Cli.host_var(host(), "TOOL_FLAG", "false"),
    ["--flag"]) == ok([
      field("flag", ["true"], Cli.Argv{}),
      field("value", ["fallback"], Cli.Default{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(sourced(), Cli.host_var(host(), "TOOL_VERBOSE", "7"),
    ["--verbose", "--verbose"]) == ok([
      field("verbose", ["2"], Cli.Argv{}),
      field("value", ["fallback"], Cli.Default{}),
    ]) : Cli.ParseResult}

# G-SRC: an invalid environment fallback is E11 with its name and reason.
law g_src_invalid:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--value <V>", "Value", [Cli.as_nat(), Cli.env("TOOL_VALUE")]),
  ]), Cli.host_var(host(), "TOOL_VALUE", "nope"), []) ==
    Cli.Rejected{[], Cli.E11{"--value <V>", "nope", "TOOL_VALUE",
      "expected a whole number from 0 to 281474976710655"}}
    : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--flag", "Flag", [Cli.env("TOOL_FLAG")]),
  ]), Cli.host_var(host(), "TOOL_FLAG", "maybe"), []) ==
    Cli.Rejected{[], Cli.E11{"--flag", "maybe", "TOOL_FLAG",
      "expected true or false"}} : Cli.ParseResult}

# G-REL: C3 lists every missing required item in declaration order.
law g_rel_required:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--out <O>", "Output", [Cli.required()]),
    Cli.arg("<FILE>", "File", []),
    Cli.arg("--ok", "Ready", []),
  ]), host(), ["--ok"]) ==
    Cli.Rejected{[], Cli.E06{["--out <O>", "<FILE>"]}}
    : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--out <O>", "Output", [Cli.required(), Cli.env("TOOL_OUT")]),
  ]), Cli.host_var(host(), "TOOL_OUT", "env"), []) == ok([
    field("out", ["env"], Cli.Env{}),
  ]) : Cli.ParseResult}

# G-REL: need_one names the group's members when none are present.
law g_rel_need_one:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.need_one("pick"),
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
  ]), host(), ["--help"]) ==
    Cli.HelpRequested{[], True{}} : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.need_one("pick"),
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
  ]), host(), ["--", "x"]) ==
    Cli.Rejected{[], Cli.E09{"x"}} : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.need_one("pick"),
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
    Cli.arg("--ok", "Ready", []),
  ]), host(), ["--ok"]) ==
    Cli.Rejected{[], Cli.E06{["<--a|--b>"]}} : Cli.ParseResult}

# G-REL: exclusive selects the later-present member as the first E07 field.
law g_rel_exclusive:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.exclusive("pick"),
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
  ]), host(), ["--a", "--b"]) ==
    Cli.Rejected{[], Cli.E07{"--b", "--a"}} : Cli.ParseResult}

# G-REL: argv presence precedes env presence for C4, then declaration order.
law g_rel_conflict_order:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--a <A>", "A", [
      Cli.env("TOOL_A"), Cli.conflicts("b")]),
    Cli.arg("--b <B>", "B", []),
  ]), Cli.host_var(host(), "TOOL_A", "env"), ["--b=argv"]) ==
    Cli.Rejected{[], Cli.E07{"--a <A>", "--b <B>"}}
    : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.conflicts("b")]),
    Cli.arg("--b", "B", []),
  ]), host(), ["--b", "--a"]) ==
    Cli.Rejected{[], Cli.E07{"--a", "--b"}} : Cli.ParseResult}

# G-REL: requires uses argv and env presence; missing targets produce E08.
law g_rel_requires:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.requires("b")]),
    Cli.arg("--b <B>", "B", [Cli.env("TOOL_B")]),
  ]), host(), ["--a"]) ==
    Cli.Rejected{[], Cli.E08{"--a", "--b <B>"}}
    : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.requires("b")]),
    Cli.arg("--b <B>", "B", [Cli.env("TOOL_B")]),
  ]), Cli.host_var(host(), "TOOL_B", "env"), ["--a"]) == ok([
    field("a", ["true"], Cli.Argv{}),
    field("b", ["env"], Cli.Env{}),
  ]) : Cli.ParseResult}

# G-REL: defaults yield values but do not satisfy or trigger relations.
law g_rel_defaults:
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--a <A>", "A", [
      Cli.default("a"), Cli.conflicts("b")]),
    Cli.arg("--b <B>", "B", [Cli.default("b")]),
  ]), host(), ["--b=argv"]) == ok([
    field("a", ["a"], Cli.Default{}),
    field("b", ["argv"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.requires("b")]),
    Cli.arg("--b <B>", "B", [Cli.default("b")]),
  ]), host(), ["--a"]) ==
    Cli.Rejected{[], Cli.E08{"--a", "--b <B>"}}
    : Cli.ParseResult}

# A decoder's Bug message, if it raises one.
def bug_of(-A: Type, d: Cli.Dec(A)) -> Maybe<&2, String>:
  match d:
    case Fail{Cli.Bug{msg}}: Some{msg}
    case _: None{}

def choose_table(keys: List<&2, String>) -> List<(String & String)>:
  match keys:
    case Nil{}: Nil{}
    case +key <> tail: (key, key) <> choose_table(tail)

def keep_table(keys: List<&2, String>) ->
    List<(String & (@+m: Cli.Matches -> Cli.Dec(Cli.Matches)))>:
  match keys:
    case Nil{}: Nil{}
    case key <> tail: (key, +m => Cli.keep(m)) <> keep_table(tail)

# Every reader's Bug for id; keys build the choose and route tables.
def reader_bugs(+m: Cli.Matches, +id: String,
    +keys: List<&2, String>) -> List<&2, Maybe<&2, String>>:
  [
    bug_of(Bool, Cli.flag(m, id)),
    bug_of(Nat, Cli.count(m, id)),
    bug_of(String, Cli.str(m, id)),
    bug_of(Maybe<&2, String>, Cli.str_opt(m, id)),
    bug_of(List<&2, String>, Cli.strs(m, id)),
    bug_of(Nat, Cli.nat(m, id)),
    bug_of(Maybe<&2, Nat>, Cli.nat_opt(m, id)),
    bug_of(List<&2, Nat>, Cli.nats(m, id)),
    bug_of(U32, Cli.u32(m, id)),
    bug_of(Maybe<&2, U32>, Cli.u32_opt(m, id)),
    bug_of(List<&2, U32>, Cli.u32s(m, id)),
    bug_of(F32, Cli.f32(m, id)),
    bug_of(Maybe<&2, F32>, Cli.f32_opt(m, id)),
    bug_of(List<&2, F32>, Cli.f32s(m, id)),
    bug_of(Bool, Cli.bool(m, id)),
    bug_of(Maybe<&2, Bool>, Cli.bool_opt(m, id)),
    bug_of(List<&2, Bool>, Cli.bools(m, id)),
    bug_of(Bool, Cli.given(m, id)),
    bug_of(Cli.Src, Cli.source(m, id)),
    bug_of(String, Cli.choose(String, m, id, choose_table(keys))),
    bug_of(Maybe<&2, String>,
      Cli.choose_opt(String, m, id, choose_table(keys))),
    bug_of(Cli.Matches, Cli.route(Cli.Matches, m, keep_table(keys))),
  ]

def p12_at(c: Cli.Cmd, found: Maybe<&2, Cli.Matches>, +id: String,
    +keys: List<&2, String>) -> Type:
  match found:
    case None{}: Unit
    case Some{+m}:
      {reader_bugs(m, id, keys)
        == reader_bugs(Cli.sample(c, Cli.path(m)), id, keys)
        : List<&2, Maybe<&2, String>>}

# P12: after any successful parse, each reader, choose and route raises the
# same validation Bug, or none, as on the parsed path's sample, whatever the
# argv. These route callbacks always succeed, so P12 covers route-table
# validation; G-READ pins what a selected callback returns.
law p12:
  for +c: Cli.Cmd
  for h: Cli.Host
  for argv: List<&2, String>
  for id: String
  for keys: List<&2, String>
  p12_at(c, Cli.matches(c, Cli.parse(c, h, argv)), id, keys)

def kinds() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-f, --flag", "Flag", []),
    Cli.arg("--[no-]neg", "Negatable", [Cli.default("true")]),
    Cli.arg("-v, --verbose...", "Verbosity", []),
    Cli.arg("--key <K>", "Key", [Cli.required()]),
    Cli.arg("--out <O>", "Output", []),
    Cli.arg("--name <N>", "Name", [Cli.default("anon")]),
    Cli.arg("--tag <T>...", "Tags", [Cli.delim(',')]),
    Cli.arg("--jobs <N>", "Jobs", [Cli.as_nat(), Cli.default("4")]),
    Cli.arg("--port <P>", "Port", [Cli.as_u32()]),
    Cli.arg("--pid <P>...", "Process ids", [Cli.as_u32()]),
    Cli.arg("--ok <B>", "Ok", [Cli.as_bool(), Cli.env("TOOL_OK")]),
    Cli.arg("--format <F>", "Format",
      [Cli.one_of(["text", "json"]), Cli.default("text")]),
    Cli.arg("--mode <M>", "Mode", [Cli.one_of(["fast", "slow"])]),
    Cli.arg("--rate <R>", "Rate", [Cli.as_f32()]),
    Cli.arg("<FILE>", "File", []),
  ])

# G-CHECK: an id must be in the sample's scope; on descent a parent's
# non-global args leave the scope and its globals stay.
law g_check_wrong_id:
  {Cli.check(~Bool, ~(+m => Cli.flag(m, "nope")), flags()) == [
    Cli.DecodeBug{"tool", "'nope' is not an argument of 'tool'"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~(+m => Cli.flag(m, "child")), sub_tool()) == [
    Cli.DecodeBug{"tool alpha beta",
      "'child' is not an argument of 'tool alpha beta'"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~(+m => Cli.flag(m, "global")), sub_tool()) ==
    [] : List<&2, Cli.Problem>}

# G-CHECK: a reader that does not fit names the arg's kind and the reader
# that fits it.
law g_check_wrong_reader:
  {Cli.check(~Nat, ~(+m => Cli.count(m, "flag")), kinds()) == [
    Cli.DecodeBug{"tool", "'flag' is a flag; read it with Cli.flag"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~(+m => Cli.flag(m, "verbose")), kinds()) == [
    Cli.DecodeBug{"tool", "'verbose' is a count; read it with Cli.count"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~String, ~(+m => Cli.str(m, "tag")), kinds()) == [
    Cli.DecodeBug{"tool",
      "'tag' is a list of string values; read it with Cli.strs"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~String, ~(+m => Cli.str(m, "jobs")), kinds()) == [
    Cli.DecodeBug{"tool", "'jobs' is a nat value; read it with Cli.nat"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Nat, ~(+m => Cli.nat(m, "port")), kinds()) == [
    Cli.DecodeBug{"tool", "'port' is a u32 value; read it with Cli.u32_opt"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Maybe<&2, U32>, ~(+m => Cli.u32_opt(m, "rate")), kinds()) == [
    Cli.DecodeBug{"tool", "'rate' is an f32 value; read it with Cli.f32_opt"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~String, ~(+m => Cli.choose(String, m, "name",
    [("anon", "anon")])), kinds()) == [
    Cli.DecodeBug{"tool", "'name' is a string value; read it with Cli.str"},
  ] : List<&2, Cli.Problem>}

def always(+m: Cli.Matches) -> Cli.Dec(String):
  do Cli.Dec<String>:
    key : String <- Cli.str(m, "key")
    name : String <- Cli.str(m, "name")
    jobs : Nat <- Cli.nat(m, "jobs")
    format : String <- Cli.choose(String, m, "format",
      [("text", "text"), ("json", "json")])
    file : String <- Cli.str(m, "file")
    named : Maybe<&2, String> <- Cli.str_opt(m, "name")
    return file

# G-CHECK: a bare reader needs a value on every parse: required(), a default,
# or a required positional. _opt fits any single-valued arg.
law g_check_absent:
  {Cli.check(~String, ~(+m => Cli.str(m, "out")), kinds()) == [
    Cli.DecodeBug{"tool", "'out' may be absent; read it with Cli.str_opt"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~String, ~(+m => Cli.choose(String, m, "mode",
    [("fast", "fast"), ("slow", "slow")])), kinds()) == [
    Cli.DecodeBug{"tool",
      "'mode' may be absent; read it with Cli.choose_opt"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~String, ~always, kinds()) == [] : List<&2, Cli.Problem>}

# G-CHECK: choose keys must equal the one_of values as a set, in any order,
# repeats allowed.
law g_check_choose:
  {Cli.check(~String, ~(+m => Cli.choose(String, m, "format",
    [("text", "text")])), kinds()) == [
    Cli.DecodeBug{"tool", "choose table for 'format' does not match its values"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~String, ~(+m => Cli.choose(String, m, "format",
    [("text", "text"), ("json", "json"), ("xml", "xml")])), kinds()) == [
    Cli.DecodeBug{"tool", "choose table for 'format' does not match its values"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~String, ~(+m => Cli.choose(String, m, "format",
    [("json", "json"), ("text", "first"), ("text", "second")])), kinds()) ==
    [] : List<&2, Cli.Problem>}

def routed() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.sub("a", "A", [Cli.alias("x")]),
    Cli.sub("b", "B", [Cli.sub("c", "C", [])]),
    Cli.completions(),
  ])

# G-CHECK: each sample's path needs a route key, checked first; every key must
# name a declared command path, and may repeat. Aliases and completions()
# are not routes.
law g_check_route:
  {Cli.check(~Cli.Matches, ~(+m => Cli.route(Cli.Matches, m,
    keep_table(["a", "z"]))), routed()) == [
    Cli.DecodeBug{"tool a", "route 'z' is not a command"},
    Cli.DecodeBug{"tool b c", "no route for 'tool b c'"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Matches, ~(+m => Cli.route(Cli.Matches, m,
    keep_table(["a", "b c", "b", "a"]))), routed()) ==
    [] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Matches, ~(+m => Cli.route(Cli.Matches, m,
    keep_table(["x", "b c"]))), routed()) == [
    Cli.DecodeBug{"tool a", "no route for 'tool a'"},
    Cli.DecodeBug{"tool b c", "route 'x' is not a command"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Matches, ~(+m => Cli.route(Cli.Matches, m,
    keep_table(["a", "b c", "completions"]))), routed()) == [
    Cli.DecodeBug{"tool a", "route 'completions' is not a command"},
    Cli.DecodeBug{"tool b c", "route 'completions' is not a command"},
  ] : List<&2, Cli.Problem>}

def tree() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [Cli.sub_optional(),
    Cli.sub("a", "A", [
      Cli.sub("b", "B", []),
      Cli.sub("c", "C", [Cli.external(),
        Cli.sub("d", "D", [Cli.hidden()]),
      ]),
    ]),
    Cli.completions(),
    Cli.man(),
  ])

# G-CHECK: one sample per path that can complete, in pre-order, skipping the
# completions() and man() built-ins; Usage faults are not problems.
law g_check_samples:
  {Cli.check(~Bool, ~(+m => Cli.bug(Bool, "b")), tree()) == [
    Cli.DecodeBug{"tool", "b"},
    Cli.DecodeBug{"tool a b", "b"},
    Cli.DecodeBug{"tool a c", "b"},
    Cli.DecodeBug{"tool a c d", "b"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~(+m => Cli.fail(Bool, "u")), tree()) ==
    [] : List<&2, Cli.Problem>}

def lookalikes() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.sub("man", "Manual pages", []),
    Cli.sub("completions", "Completion data", []),
  ])

# G-CHECK: only completions() and man() are built-ins; a sub() that shares a
# name with one is an ordinary command, with a sample and a route.
law g_check_builtins:
  {Cli.check(~Bool, ~(+m => Cli.bug(Bool, "b")), lookalikes()) == [
    Cli.DecodeBug{"tool man", "b"},
    Cli.DecodeBug{"tool completions", "b"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Matches, ~(+m => Cli.route(Cli.Matches, m,
    keep_table(["man", "completions"]))), lookalikes()) ==
    [] : List<&2, Cli.Problem>}

def sampled() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-v, --verbose...", "Verbosity", [Cli.global()]),
    Cli.arg("--root <R>", "Root only", []),
    Cli.sub("s", "S", [
      Cli.arg("--flag", "Flag", []),
      Cli.arg("--[no-]pos", "Positive", []),
      Cli.arg("--[no-]neg", "Negatable", [Cli.default("false")]),
      Cli.arg("--name <N>", "Name",
        [Cli.env("TOOL_NAME"), Cli.default("anon")]),
      Cli.arg("--mode <M>", "Mode", [Cli.one_of(["fast", "slow"])]),
      Cli.arg("--num <N>", "Nat", [Cli.as_nat()]),
      Cli.arg("--uint <U>", "U32", [Cli.as_u32()]),
      Cli.arg("--real <F>", "F32", [Cli.as_f32()]),
      Cli.arg("--yes <B>", "Bool", [Cli.as_bool()]),
      Cli.arg("--tag <T>...", "Tags", [Cli.delim(','), Cli.default("a,b")]),
      Cli.arg("<FILE>...", "Files", [Cli.as_file()]),
    ]),
  ])

type Sampled is Data:
  Sampled{verbose: Nat, flag: Bool, pos: Bool, neg: Bool, name: String,
    mode: Maybe<&2, String>, num: Maybe<&2, Nat>, uint: Maybe<&2, U32>,
    yes: Maybe<&2, Bool>, tags: List<&2, String>, files: List<&2, String>,
    name_source: Cli.Src, mode_source: Cli.Src, real_source: Cli.Src}

def read_sample(+m: Cli.Matches) -> Cli.Dec(Sampled):
  do Cli.Dec<Sampled>:
    verbose : Nat <- Cli.count(m, "verbose")
    flag : Bool <- Cli.flag(m, "flag")
    pos : Bool <- Cli.flag(m, "pos")
    neg : Bool <- Cli.flag(m, "neg")
    name : String <- Cli.str(m, "name")
    mode : Maybe<&2, String> <- Cli.str_opt(m, "mode")
    num : Maybe<&2, Nat> <- Cli.nat_opt(m, "num")
    uint : Maybe<&2, U32> <- Cli.u32_opt(m, "uint")
    yes : Maybe<&2, Bool> <- Cli.bool_opt(m, "yes")
    tags : List<&2, String> <- Cli.strs(m, "tag")
    files : List<&2, String> <- Cli.strs(m, "file")
    name_source : Cli.Src <- Cli.source(m, "name")
    mode_source : Cli.Src <- Cli.source(m, "mode")
    real_source : Cli.Src <- Cli.source(m, "real")
    return Sampled{verbose, flag, pos, neg, name, mode, num, uint, yes, tags,
      files, name_source, mode_source, real_source}

# G-CHECK: a sample holds every arg in scope, read here through readers. A
# default resolves as parse resolves it; otherwise the first one_of value,
# else a value by type; flags are true, counts 1, lists one element. A
# sample f32 has no value golden (K8); its source shows it is present.
law g_check_sample_values:
  {read_sample(Cli.sample(sampled(), ["s"])) == Done{Sampled{1n, True{},
    True{}, False{}, "anon", Some{"fast"}, Some{0n}, Some{0}, Some{False{}},
    ["a", "b"], ["x"], Cli.Default{}, Cli.Argv{}, Cli.Argv{}}}
    : Cli.Dec(Sampled)}

# G-CHECK: the pkg demo's decoder raises no Bug on any sample.
law g_check_pkg:
  {Cli.check(~Demo.Action, ~Demo.decode, Demo.cli()) ==
    [] : List<&2, Cli.Problem>}

# G-LINT DecodeBug: check lists lint problems first, then decode bugs.
law g_lint_decode_bug:
  {Cli.check(~Bool, ~(+m => Cli.flag(m, "nope")), Cli.cmd("tool", "Tool", [
    Cli.arg("--quiet", "", []),
  ])) == [
    Cli.NoHelp{"tool", "--quiet"},
    Cli.DecodeBug{"tool", "'nope' is not an argument of 'tool'"},
  ] : List<&2, Cli.Problem>}

def decode_found(~A: Type, ~decode: @+m: Cli.Matches -> Cli.Dec(A),
    found: Maybe<&2, Cli.Matches>) -> Maybe<Cli.Dec(A)>:
  match found:
    case None{}: None{}
    case Some{+m}: Some{decode(m)}

# What decode answers for argv, or None when the parse does not succeed.
def decoded(~A: Type, ~decode: @+m: Cli.Matches -> Cli.Dec(A), +c: Cli.Cmd,
    h: Cli.Host, argv: List<&2, String>) -> Maybe<Cli.Dec(A)>:
  decode_found(~A, ~decode, Cli.matches(c, Cli.parse(c, h, argv)))

type Readout is Data:
  Readout{flag: Bool, neg: Bool, verbose: Nat, key: String,
    out: Maybe<&2, String>, name: String, tags: List<&2, String>, jobs: Nat,
    port: Maybe<&2, U32>, pids: List<&2, U32>, ok: Maybe<&2, Bool>,
    format: String, mode: Maybe<&2, String>, rate: Maybe<&2, F32>,
    file: String, ok_given: Bool, name_source: Cli.Src, ok_source: Cli.Src}

def readout(+m: Cli.Matches) -> Cli.Dec(Readout):
  do Cli.Dec<Readout>:
    flag : Bool <- Cli.flag(m, "flag")
    neg : Bool <- Cli.flag(m, "neg")
    verbose : Nat <- Cli.count(m, "verbose")
    key : String <- Cli.str(m, "key")
    out : Maybe<&2, String> <- Cli.str_opt(m, "out")
    name : String <- Cli.str(m, "name")
    tags : List<&2, String> <- Cli.strs(m, "tag")
    jobs : Nat <- Cli.nat(m, "jobs")
    port : Maybe<&2, U32> <- Cli.u32_opt(m, "port")
    pids : List<&2, U32> <- Cli.u32s(m, "pid")
    ok : Maybe<&2, Bool> <- Cli.bool_opt(m, "ok")
    format : String <- Cli.choose(String, m, "format",
      [("text", "plain"), ("json", "structured")])
    mode : Maybe<&2, String> <- Cli.choose_opt(String, m, "mode",
      [("fast", "F"), ("slow", "S")])
    rate : Maybe<&2, F32> <- Cli.f32_opt(m, "rate")
    file : String <- Cli.str(m, "file")
    ok_given : Bool <- Cli.given(m, "ok")
    name_source : Cli.Src <- Cli.source(m, "name")
    ok_source : Cli.Src <- Cli.source(m, "ok")
    return Readout{flag, neg, verbose, key, out, name, tags, jobs, port, pids,
      ok, format, mode, rate, file, ok_given, name_source, ok_source}

def forms() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--depth <D>", "Depth", [Cli.as_nat()]),
    Cli.arg("--size <N>...", "Sizes", [Cli.as_nat()]),
    Cli.arg("--seed <S>", "Seed", [Cli.as_u32(), Cli.default("7")]),
    Cli.arg("--strict <B>", "Strict", [Cli.as_bool(), Cli.default("off")]),
    Cli.arg("--bit <B>...", "Bits", [Cli.as_bool(), Cli.delim(',')]),
    Cli.arg("--level <L>", "Level",
      [Cli.one_of(["low", "high"]), Cli.default("low")]),
    Cli.arg("--ratio <R>...", "Ratios", [Cli.as_f32()]),
  ])

type Forms is Data:
  Forms{depth: Maybe<&2, Nat>, sizes: List<&2, Nat>, seed: U32, strict: Bool,
    bits: List<&2, Bool>, level: String, ratios: List<&2, F32>}

def read_forms(+m: Cli.Matches) -> Cli.Dec(Forms):
  do Cli.Dec<Forms>:
    depth : Maybe<&2, Nat> <- Cli.nat_opt(m, "depth")
    sizes : List<&2, Nat> <- Cli.nats(m, "size")
    seed : U32 <- Cli.u32(m, "seed")
    strict : Bool <- Cli.bool(m, "strict")
    bits : List<&2, Bool> <- Cli.bools(m, "bit")
    level : String <- Cli.str(m, "level")
    ratios : List<&2, F32> <- Cli.f32s(m, "ratio")
    return Forms{depth, sizes, seed, strict, bits, level, ratios}

# G-READ: each reader returns its parsed value; choose returns the table's
# value for the key. A given f32 has no golden: F32.read does not normalize
# in the checker (K8), so end-to-end tests cover it.
law g_read_values:
  {decoded(~Readout, ~readout, kinds(), Cli.host_var(host(), "TOOL_OK", "yes"),
    ["-f", "--no-neg", "-vv", "--key", "k", "--out", "o", "--tag=a,b",
      "--tag", "c", "--jobs", "8", "--port", "8080", "--pid=1", "--pid=2",
      "--format", "json", "--mode", "slow", "in"]) ==
    Some{Done{Readout{True{}, False{}, 2n, "k", Some{"o"}, "anon",
      ["a", "b", "c"], 8n, Some{8080}, [1, 2], Some{True{}}, "structured",
      Some{"S"}, None{}, "in", True{}, Cli.Default{}, Cli.Env{}}}}
    : Maybe<Cli.Dec(Readout)>} &
  {decoded(~Forms, ~read_forms, forms(), host(),
    ["--depth", "2", "--size=3", "--size", "5", "--seed", "4294967295",
      "--strict=YES", "--bit=1,no,TRUE", "--level", "high"]) ==
    Some{Done{Forms{Some{2n}, [3n, 5n], 4294967295, True{},
      [True{}, False{}, True{}], "high", []}}}
    : Maybe<Cli.Dec(Forms)>}

# G-READ: absent args read as their default, else False, 0, None or [].
law g_read_absent:
  {decoded(~Readout, ~readout, kinds(), host(), ["--key", "k", "in"]) ==
    Some{Done{Readout{False{}, True{}, 0n, "k", None{}, "anon", [], 4n,
      None{}, [], None{}, "plain", None{}, None{}, "in", False{},
      Cli.Default{}, Cli.Absent{}}}}
    : Maybe<Cli.Dec(Readout)>} &
  {decoded(~Forms, ~read_forms, forms(), host(), []) ==
    Some{Done{Forms{None{}, [], 7, False{}, [], "low", []}}}
    : Maybe<Cli.Dec(Forms)>}

def rooted() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [Cli.sub_optional(),
    Cli.sub("a", "A", [Cli.alias("x"), Cli.sub("b", "B", [])]),
  ])

def which(+m: Cli.Matches) -> Cli.Dec(String):
  Cli.route(String, m, [
    ("", +n => Done{"root"}),
    ("a b", +n => Done{"a b"}),
  ])

def kept_path(+m: Cli.Matches) -> Cli.Dec(List<&2, String>):
  do Cli.Dec<List<&2, String>>:
    k : Cli.Matches <- Cli.keep(m)
    return Cli.path(k)

# G-READ: route dispatches on the canonical path, the root at "";
# keep returns its input, whose path names the declared commands.
law g_read_route:
  {decoded(~String, ~which, rooted(), host(), []) ==
    Some{Done{"root"}} : Maybe<Cli.Dec(String)>} &
  {decoded(~String, ~which, rooted(), host(), ["x", "b"]) ==
    Some{Done{"a b"}} : Maybe<Cli.Dec(String)>} &
  {decoded(~List<&2, String>, ~kept_path, rooted(), host(), ["x", "b"]) ==
    Some{Done{["a", "b"]}} : Maybe<Cli.Dec(List<&2, String>)>}

def first_choice(+m: Cli.Matches) -> Cli.Dec(String):
  Cli.choose(String, m, "format",
    [("json", "json"), ("text", "first"), ("text", "second")])

def first_route(+m: Cli.Matches) -> Cli.Dec(String):
  Cli.route(String, m, [
    ("a b", +n => Done{"a b"}),
    ("", +n => Done{"first"}),
    ("", +n => Done{"second"}),
  ])

# G-READ: when a choose or route key repeats, the first matching entry wins.
law g_read_first_match:
  {decoded(~String, ~first_choice, kinds(), host(), ["--key", "k", "in"]) ==
    Some{Done{"first"}} : Maybe<Cli.Dec(String)>} &
  {decoded(~String, ~first_route, rooted(), host(), []) ==
    Some{Done{"first"}} : Maybe<Cli.Dec(String)>}

def faults(+m: Cli.Matches) -> Cli.Dec(String):
  Cli.route(String, m, [
    ("", +n => Cli.bug(String, "root bug")),
    ("a b", +n => Cli.fail(String, "a b usage")),
  ])

def bad_faults(+m: Cli.Matches) -> Cli.Dec(String):
  Cli.route(String, m, [
    ("", +n => Cli.bug(String, "root bug")),
    ("a b", +n => Cli.fail(String, "a b usage")),
    ("z", +n => Done{"z"}),
  ])

# G-READ: route validates its whole table, then returns the selected
# callback's result unchanged, Bug and Usage included; check reports a
# callback's Bug at its sample.
law g_read_route_faults:
  {decoded(~String, ~faults, rooted(), host(), []) ==
    Some{Fail{Cli.Bug{"root bug"}}} : Maybe<Cli.Dec(String)>} &
  {decoded(~String, ~faults, rooted(), host(), ["x", "b"]) ==
    Some{Fail{Cli.Usage{"a b usage"}}} : Maybe<Cli.Dec(String)>} &
  {decoded(~String, ~bad_faults, rooted(), host(), []) ==
    Some{Fail{Cli.Bug{"route 'z' is not a command"}}}
    : Maybe<Cli.Dec(String)>} &
  {Cli.check(~String, ~faults, rooted()) == [
    Cli.DecodeBug{"tool", "root bug"},
  ] : List<&2, Cli.Problem>}

# G-READ: external_args holds the unknown name and the tokens after it.
law g_read_external:
  {decoded(~Maybe<(String & List<&2, String>)>,
    ~(+m => Done{Cli.external_args(m)}), external_tool(), host(),
    ["plug", "--x"]) == Some{Done{Some{("plug", ["--x"])}}}
    : Maybe<Cli.Dec(Maybe<(String & List<&2, String>)>)>} &
  {decoded(~Maybe<(String & List<&2, String>)>,
    ~(+m => Done{Cli.external_args(m)}), external_tool(), host(),
    ["known"]) == Some{Done{None{}}}
    : Maybe<Cli.Dec(Maybe<(String & List<&2, String>)>)>}

# G-READ: pkg decodes globals before and after the subcommand, an env
# registry, an alias, a choose, and rest() arguments.
law g_read_pkg:
  {decoded(~Demo.Action, ~Demo.decode, Demo.cli(),
    Cli.host_var(host(), "PKG_REGISTRY", "https://mirror.example"),
    ["-vv", "add", "-D", "left-pad"]) ==
    Some{Done{Demo.Action{2n, None{}, Demo.Add{True{},
      "https://mirror.example", ["left-pad"]}}}}
    : Maybe<Cli.Dec(Demo.Action)>} &
  {decoded(~Demo.Action, ~Demo.decode, Demo.cli(), host(),
    ["rm", "a", "-C", "/srv", "b"]) ==
    Some{Done{Demo.Action{0n, Some{"/srv"}, Demo.Remove{["a", "b"]}}}}
    : Maybe<Cli.Dec(Demo.Action)>} &
  {decoded(~Demo.Action, ~Demo.decode, Demo.cli(), host(),
    ["list", "--format", "json", "-a"]) ==
    Some{Done{Demo.Action{0n, None{}, Demo.Show{True{}, Demo.Json{}}}}}
    : Maybe<Cli.Dec(Demo.Action)>} &
  {decoded(~Demo.Action, ~Demo.decode, Demo.cli(), host(),
    ["run", "build", "x", "--", "-y"]) ==
    Some{Done{Demo.Action{0n, None{}, Demo.Script{"build",
      ["x", "--", "-y"]}}}}
    : Maybe<Cli.Dec(Demo.Action)>}

# M4: outcome is eval's answer before decoding (V1-V5): Shown is the exit
# code and the bytes for stdout and stderr; Matched is a parse to decode.
# term is the color and width that outcome, help and Go use.

# The colors term decides, stdout first.
def colors(t: Cli.Term) -> (Bool & Bool):
  match t:
    case Cli.Term{out_color, err_color, width}: (out_color, err_color)

# Whether a token before the first `--` spells --color, in either form.
def names_color(argv: List<&2, String>) -> Bool:
  match argv:
    case Nil{}: False{}
    case +token <> tail:
      Bool.and(Bool.not(String.eq(token, "--")),
        Bool.or(Bool.or(String.eq(token, "--color"),
          String.starts_with(token, "--color=")), names_color(tail)))

def set_nonempty(found: Maybe<&2, String>) -> Bool:
  match found:
    case None{}: False{}
    case Some{value}: Bool.not(String.is_empty(value))

# P7: a non-empty NO_COLOR turns both streams off unless argv spells --color
# before its first `--`.
law p7:
  for c: Cli.Cmd
  for +h: Cli.Host
  for +argv: List<&2, String>
  {set_nonempty(Cli.host_value(h, "NO_COLOR")) == True{} : Bool} ->
  {names_color(argv) == False{} : Bool} ->
  {colors(Cli.term(c, h, argv)) == (False{}, False{}) : (Bool & Bool)}

def colors_around(c: Cli.Cmd, h: Cli.Host, pre: List<&2, String>,
    post: List<&2, String>, chosen: List<&2, String>) -> (Bool & Bool):
  colors(Cli.term(c, h, List.append(&2, String, pre,
    List.append(&2, String, chosen, post))))

# The colors for pre ++ chosen ++ post, for each spelling of never and always.
def p8_colors(+c: Cli.Cmd, +h: Cli.Host, +pre: List<&2, String>,
    +post: List<&2, String>) -> List<(Bool & Bool)>:
  [
    colors_around(c, h, pre, post, ["--color=never"]),
    colors_around(c, h, pre, post, ["--color=always"]),
    colors_around(c, h, pre, post, ["--color", "never"]),
    colors_around(c, h, pre, post, ["--color", "always"]),
  ]

# P8: in an app with color(), the last --color before `--` decides both
# streams on every host: never turns color off and always turns it on.
law p8:
  for name: String
  for about: String
  for before: List<&2, Cli.Item>
  for after: List<&2, Cli.Item>
  for h: Cli.Host
  for +pre: List<&2, String>
  for +post: List<&2, String>
  {List.contains(~String, ~String.eq, pre, "--") == False{} : Bool} ->
  {names_color(post) == False{} : Bool} ->
  {p8_colors(Cli.cmd(name, about,
    List.append(&2, Cli.Item, before, Cli.color() <> after)), h, pre, post)
    == [(False{}, False{}), (True{}, True{}), (False{}, False{}),
      (True{}, True{})] : List<(Bool & Bool)>}

# Text as printed: each line ends with a newline.
def page(lines: List<&2, String>) -> String:
  match lines:
    case Nil{}: ""
    case line <> tail: String.concat([line, "\n", page(tail)])

def pkg_page() -> String:
  page([
    "A package manager (demo)",
    "",
    "Usage: pkg [OPTIONS] <COMMAND>",
    "",
    "Commands:",
    "  add                 Add packages",
    "  remove              Remove packages [aliases: rm]",
    "  list                List installed packages",
    "  run                 Run a package script",
    "  completions         Print a shell completion script",
    "  help                Print this message or the help of the given subcommand(s)",
    "",
    "Options:",
    "      --color <WHEN>  When to use color [default: auto] [possible values: auto,",
    "                      always, never]",
    "  -v, --verbose...    More output; repeat for more",
    "  -C <DIR>            Run as if started in DIR",
    "  -h, --help          Print help",
    "  -V, --version       Print version",
  ])

# G-HELP: the root page lists visible subcommands with the help subcommand
# last, then options: own, inherited globals, then help and version. Long-only
# options indent 4 more. With no two-paragraph text, -h and --help agree.
law g_help_root:
  {Cli.help(Demo.cli(), [], False{}, host()) == pkg_page() : String} &
  {Cli.help(Demo.cli(), [], True{}, host()) == pkg_page() : String}

def add_page() -> String:
  page([
    "Add packages",
    "",
    "Usage: pkg add [OPTIONS] <NAME>...",
    "",
    "Arguments:",
    "  <NAME>...             Packages to add",
    "",
    "Options:",
    "  -D, --dev             Add as development dependencies",
    "      --registry <URL>  Registry to fetch from [env: PKG_REGISTRY] [default:",
    "                        https://registry.example]",
    "      --color <WHEN>    When to use color [default: auto] [possible values:",
    "                        auto, always, never]",
    "  -v, --verbose...      More output; repeat for more",
    "  -C <DIR>              Run as if started in DIR",
    "  -h, --help            Print help",
    "",
    "Examples:",
    "  Add a development dependency:",
    "    $ pkg add -D left-pad",
  ])

# G-HELP: a subcommand page lists arguments, its own options, the root's
# globals and help. help and usage render the longest valid prefix of path.
law g_help_sub:
  {Cli.help(Demo.cli(), ["add"], False{}, host()) == add_page() : String} &
  {Cli.help(Demo.cli(), ["add", "nope"], True{}, host())
    == add_page() : String} &
  {Cli.usage(Demo.cli(), ["add"]) == "pkg add [OPTIONS] <NAME>..." : String} &
  {Cli.usage(Demo.cli(), ["nope"]) == "pkg [OPTIONS] <COMMAND>" : String}

# G-HELP: W clamps host width to 40 and 100. At 40, a left cell wider than
# K - 4 = 12 stands alone, and its text starts on the next line at C = 15.
law g_help_width:
  {Cli.help(Demo.cli(), [], False{}, Cli.host(30n)) == page([
    "A package manager (demo)",
    "",
    "Usage: pkg [OPTIONS] <COMMAND>",
    "",
    "Commands:",
    "  add          Add packages",
    "  remove       Remove packages [aliases:",
    "               rm]",
    "  list         List installed packages",
    "  run          Run a package script",
    "  completions  Print a shell completion",
    "               script",
    "  help         Print this message or the",
    "               help of the given",
    "               subcommand(s)",
    "",
    "Options:",
    "      --color <WHEN>",
    "               When to use color",
    "               [default: auto] [possible",
    "               values: auto, always,",
    "               never]",
    "  -v, --verbose...",
    "               More output; repeat for",
    "               more",
    "  -C <DIR>     Run as if started in DIR",
    "  -h, --help   Print help",
    "  -V, --version",
    "               Print version",
  ]) : String} &
  {Cli.help(Demo.cli(), [], False{}, Cli.host(120n)) == page([
    "A package manager (demo)",
    "",
    "Usage: pkg [OPTIONS] <COMMAND>",
    "",
    "Commands:",
    "  add                 Add packages",
    "  remove              Remove packages [aliases: rm]",
    "  list                List installed packages",
    "  run                 Run a package script",
    "  completions         Print a shell completion script",
    "  help                Print this message or the help of the given subcommand(s)",
    "",
    "Options:",
    "      --color <WHEN>  When to use color [default: auto] [possible values: auto, always, never]",
    "  -v, --verbose...    More output; repeat for more",
    "  -C <DIR>            Run as if started in DIR",
    "  -h, --help          Print help",
    "  -V, --version       Print version",
  ]) : String}

def docs() -> Cli.Cmd:
  Cli.cmd("docs",
    "Render documents\n\nReads Markdown and writes HTML.\nOne file at a time.", [
    Cli.arg("-o, --out <FILE>", "Output file\n\nDefaults to standard output.",
      []),
    Cli.arg("--title <TEXT>",
      "Page title, such as 日本語 or cafe\u{301} and some more text", []),
    Cli.arg("<INPUT>", "Input file", []),
  ])

def docs_page(long: Bool) -> String:
  match long:
    case False{}:
      page([
        "Render documents",
        "",
        "Usage: docs [OPTIONS] <INPUT>",
        "",
        "Arguments:",
        "  <INPUT>     Input file",
        "",
        "Options:",
        "  -o, --out <FILE>",
        "              Output file",
        "      --title <TEXT>",
        "              Page title, such as 日本語",
        "              or cafe\u{301} and some more text",
        "  -h, --help  Print help (see more with",
        "              '--help')",
      ])
    case True{}:
      page([
        "Render documents",
        "",
        "Reads Markdown and writes HTML.",
        "One file at a time.",
        "",
        "Usage: docs [OPTIONS] <INPUT>",
        "",
        "Arguments:",
        "  <INPUT>     Input file",
        "",
        "Options:",
        "  -o, --out <FILE>",
        "              Output file",
        "",
        "              Defaults to standard",
        "              output.",
        "      --title <TEXT>",
        "              Page title, such as 日本語",
        "              or cafe\u{301} and some more text",
        "  -h, --help  Print help (see a summary",
        "              with '-h')",
      ])

# G-HELP: -h shows first paragraphs and --help all of them, keeping hard line
# breaks; the help option names the other page. Wrapping counts each CJK
# character as 2 columns and a combining mark as 0.
law g_help_paragraphs:
  {Cli.help(docs(), [], False{}, Cli.host(20n))
    == docs_page(False{}) : String} &
  {Cli.help(docs(), [], True{}, Cli.host(20n))
    == docs_page(True{}) : String}

def feat() -> Cli.Cmd:
  Cli.cmd("feat", "Feature tour", [
    Cli.arg("--mode <MODE>", "Mode", [Cli.env("FEAT_MODE"), Cli.default("fast"),
      Cli.one_of(["fast", "slow"]), Cli.alias("--speed")]),
    Cli.arg("--secret", "Hidden flag", [Cli.hidden()]),
    Cli.arg("--host <HOST>", "Server host", [Cli.heading("Network")]),
    Cli.arg("--port <PORT>", "Server port",
      [Cli.heading("Network"), Cli.as_u32()]),
    Cli.example("feat --mode slow", "Run slowly"),
    Cli.example("feat --host example.org", "Use a server"),
    Cli.after("Docs: https://example.org/feat"),
  ])

def feat_page() -> String:
  page([
    "Feature tour",
    "",
    "Usage: feat [OPTIONS]",
    "",
    "Options:",
    "      --mode <MODE>  Mode [env: FEAT_MODE] [default: fast] [possible values:",
    "                     fast, slow] [aliases: --speed]",
    "  -h, --help         Print help",
    "",
    "Network:",
    "      --host <HOST>  Server host",
    "      --port <PORT>  Server port",
    "",
    "Examples:",
    "  Run slowly:",
    "    $ feat --mode slow",
    "  Use a server:",
    "    $ feat --host example.org",
    "",
    "Docs: https://example.org/feat",
  ])

# G-HELP: tags follow env, default, possible values, aliases; a hidden arg is
# left out; a heading gets its own section after Options, with one column
# for the page; examples, then after text, close the page.
law g_help_sections:
  {Cli.help(feat(), [], False{}, host()) == feat_page() : String} &
  {Cli.help(feat(), [], True{}, host()) == feat_page() : String}

def up() -> Cli.Cmd:
  Cli.cmd("up", "Upload", [
    Cli.need_one("src"),
    Cli.arg("--token <T>", "Token", [Cli.required()]),
    Cli.arg("--file <F>", "File", [Cli.group("src")]),
    Cli.arg("--url <U>", "URL", [Cli.group("src")]),
    Cli.arg("[DEST]", "Destination", []),
  ])

# G-HELP: usage text puts required options and need_one groups, as E06 writes
# them, before positionals; it wraps between elements, continuing at 7.
law g_help_usage:
  {Cli.usage(up(), [])
    == "up [OPTIONS] --token <T> <--file <F>|--url <U>> [DEST]" : String} &
  {Cli.help(up(), [], False{}, Cli.host(30n)) == page([
    "Upload",
    "",
    "Usage: up [OPTIONS] --token <T>",
    "       <--file <F>|--url <U>> [DEST]",
    "",
    "Arguments:",
    "  [DEST]      Destination",
    "",
    "Options:",
    "      --token <T>",
    "              Token",
    "      --file <F>",
    "              File",
    "      --url <U>",
    "              URL",
    "  -h, --help  Print help",
  ]) : String}

# G-HELP: help and version go to stdout with exit 0: -h the summary page,
# --help and `help add` the full page, and the first of help and version wins
# (V1, V2). Empty argv that the root rejects shows the summary page on stderr
# with exit 2 (V3).
law g_help_outcome:
  {Cli.outcome(Demo.cli(), host(), ["-h"])
    == Cli.Shown{0, pkg_page(), ""} : Cli.Outcome} &
  {Cli.outcome(docs(), Cli.host(20n), ["-h"])
    == Cli.Shown{0, docs_page(False{}), ""} : Cli.Outcome} &
  {Cli.outcome(docs(), Cli.host(20n), ["--help"])
    == Cli.Shown{0, docs_page(True{}), ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["help", "add"])
    == Cli.Shown{0, add_page(), ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["--version"])
    == Cli.Shown{0, "pkg 0.1.0\n", ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["-V"])
    == Cli.Shown{0, "pkg 0.1.0\n", ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["-V", "--help"])
    == Cli.Shown{0, "pkg 0.1.0\n", ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["--help", "-V"])
    == Cli.Shown{0, pkg_page(), ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), [])
    == Cli.Shown{2, "", pkg_page()} : Cli.Outcome}

# G-ERR: an error is exit 2 on stderr: the message, a blank line, then the
# usage of the scope where it occurred and a pointer to --help.
law g_err_format:
  {Cli.outcome(Demo.cli(), host(), ["--bogus"]) == Cli.Shown{2, "", page([
    "error: unexpected argument '--bogus' found",
    "",
    "Usage: pkg [OPTIONS] <COMMAND>",
    "",
    "For more information, try '--help'.",
  ])} : Cli.Outcome}

def tip_lines(tips: List<&2, String>) -> String:
  match tips:
    case Nil{}: ""
    case tip <> tail: String.concat(["  tip: ", tip, "\n", tip_lines(tail)])

def tip_block(tips: List<&2, String>) -> String:
  match tips:
    case Nil{}: ""
    case tip <> tail: String.append("\n", tip_lines(tip <> tail))

# The uncolored outcome for an error: message, tips, then the scope's usage.
def report(message: String, tips: List<&2, String>,
    usage: String) -> Cli.Outcome:
  Cli.Shown{2, "", String.concat(["error: ", message, "\n", tip_block(tips),
    "\nUsage: ", usage, "\n\nFor more information, try '--help'.\n"])}

# G-ERR: each scan error's message, at the scope where scanning stopped: E02,
# E03, E04, E05, then E09 twice, the second on a hyphen token after `--`,
# which no slot takes, so T5 does not apply. g_err_format is E01.
law g_err_scan:
  {Cli.outcome(Demo.cli(), host(), ["bogus"]) ==
    report("unrecognized subcommand 'bogus'", [], "pkg [OPTIONS] <COMMAND>")
    : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["add", "--registry"]) ==
    report("a value is required for '--registry <URL>' but none was supplied",
      [], "pkg add [OPTIONS] <NAME>...") : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["list", "--format", "xml"]) ==
    report("invalid value 'xml' for '--format <FMT>': expected one of 'text', 'json'",
      [], "pkg list [OPTIONS]") : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["list", "--all=yes"]) ==
    report("unexpected value 'yes' for '--all' found; no more were expected",
      [], "pkg list [OPTIONS]") : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["list", "extra"]) ==
    report("unexpected argument 'extra' found", [], "pkg list [OPTIONS]")
    : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["list", "--", "-x"]) ==
    report("unexpected argument '-x' found", [], "pkg list [OPTIONS]")
    : Cli.Outcome}

def rel() -> Cli.Cmd:
  Cli.cmd("rel", "Relations", [
    Cli.arg("--json", "JSON output", [Cli.conflicts("yaml")]),
    Cli.arg("--yaml", "YAML output", []),
    Cli.arg("--key <KEY>", "Signing key", [Cli.requires("sign")]),
    Cli.arg("--sign", "Sign output", []),
    Cli.arg("--jobs <N>", "Parallel jobs", [Cli.as_u32(), Cli.env("REL_JOBS")]),
  ])

# G-ERR: each post-scan check's message, E06, E07, E08, E10, then E11; E06
# and E10 add indented lines, and an error message is not wrapped.
law g_err_check:
  {Cli.outcome(Demo.cli(), host(), ["add"]) == report(
    "the following required arguments were not provided:\n  <NAME>...",
    [], "pkg add [OPTIONS] <NAME>...") : Cli.Outcome} &
  {Cli.outcome(rel(), host(), ["--json", "--yaml"]) ==
    report("the argument '--yaml' cannot be used with '--json'", [],
      "rel [OPTIONS]") : Cli.Outcome} &
  {Cli.outcome(rel(), host(), ["--key", "k"]) ==
    report("the argument '--key <KEY>' requires '--sign'", [],
      "rel [OPTIONS]") : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["-v"]) == report(
    "'pkg' requires a subcommand but none was provided\n  [subcommands: add, remove, list, run, completions, help]",
    [], "pkg [OPTIONS] <COMMAND>") : Cli.Outcome} &
  {Cli.outcome(rel(), Cli.host_var(host(), "REL_JOBS", "many"), []) ==
    report("invalid value 'many' for '--jobs <N>' from environment variable REL_JOBS: expected a whole number from 0 to 4294967295",
      [], "rel [OPTIONS]") : Cli.Outcome}

def list_page() -> String:
  page([
    "List installed packages",
    "",
    "Usage: pkg list [OPTIONS]",
    "",
    "Options:",
    "  -a, --all           Include transitive packages",
    "      --format <FMT>  Output format [default: text] [possible values: text,",
    "                      json]",
    "      --color <WHEN>  When to use color [default: auto] [possible values: auto,",
    "                      always, never]",
    "  -v, --verbose...    More output; repeat for more",
    "  -C <DIR>            Run as if started in DIR",
    "  -h, --help          Print help",
  ])

# G-ERR: a later help token wins over E01, E03 and E04; E02 stops the scan
# before it.
law g_err_precedence:
  {Cli.outcome(Demo.cli(), host(), ["--bogus", "-h"])
    == Cli.Shown{0, pkg_page(), ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["add", "--registry", "--help"])
    == Cli.Shown{0, add_page(), ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["list", "--format", "xml", "-h"])
    == Cli.Shown{0, list_page(), ""} : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["bogus", "--help"]) ==
    report("unrecognized subcommand 'bogus'", [], "pkg [OPTIONS] <COMMAND>")
    : Cli.Outcome}

# G-TIP: T1 names the ancestor that owns a long, T2 the first descendant in
# pre-order, and T3 a subcommand written as a long.
law g_tip_scope:
  {Cli.outcome(sub_tool(), host(), ["alpha", "--root"]) ==
    report("unexpected argument '--root' found",
      ["'--root' belongs to 'tool'; place it before 'alpha'"],
      "tool alpha [OPTIONS] [COMMAND]") : Cli.Outcome} &
  {Cli.outcome(sub_tool(), host(), ["--child", "alpha"]) ==
    report("unexpected argument '--child' found",
      ["'--child' belongs to subcommand 'tool alpha'"],
      "tool [OPTIONS] <COMMAND>") : Cli.Outcome} &
  {Cli.outcome(sub_tool(), host(), ["--alpha"]) ==
    report("unexpected argument '--alpha' found",
      ["subcommand 'alpha' exists; to use it, remove the '--'"],
      "tool [OPTIONS] <COMMAND>") : Cli.Outcome}

# G-TIP: T4 suggests a similar argument, subcommands (aliases included) or a
# one_of value; T5 shows how to pass a hyphen token to a positional.
law g_tip_suggest:
  {Cli.outcome(Demo.cli(), host(), ["--verbos"]) ==
    report("unexpected argument '--verbos' found",
      ["a similar argument exists: '--verbose'"],
      "pkg [OPTIONS] <COMMAND>") : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["rn"]) ==
    report("unrecognized subcommand 'rn'",
      ["some similar subcommands exist: 'rm', 'run'"],
      "pkg [OPTIONS] <COMMAND>") : Cli.Outcome} &
  {Cli.outcome(Demo.cli(), host(), ["list", "--format", "jsn"]) ==
    report("invalid value 'jsn' for '--format <FMT>': expected one of 'text', 'json'",
      ["a similar value exists: 'json'"], "pkg list [OPTIONS]")
    : Cli.Outcome} &
  {Cli.outcome(cp(), host(), ["-x"]) ==
    report("unexpected argument '-x' found",
      ["to pass '-x' as a value, use '-- -x'"], "cp <SRC>... <DST>")
    : Cli.Outcome}

def rmf() -> Cli.Cmd:
  Cli.cmd("rmf", "Remove a file", [
    Cli.arg("-f, --force", "Force", []),
    Cli.arg("<FILE>", "File to remove", []),
  ])

# G-TIP: every tip that applies is shown, in table order.
law g_tip_order:
  {Cli.outcome(rmf(), host(), ["--forse"]) == Cli.Shown{2, "", page([
    "error: unexpected argument '--forse' found",
    "",
    "  tip: a similar argument exists: '--force'",
    "  tip: to pass '--forse' as a value, use '-- --forse'",
    "",
    "Usage: rmf [OPTIONS] <FILE>",
    "",
    "For more information, try '--help'.",
  ])} : Cli.Outcome}

def neg() -> Cli.Cmd:
  Cli.cmd("neg", "Negation", [Cli.arg("--[no-]safe", "Safety checks", [])])

# G-TIP: argument candidates include long aliases and no- forms, not hidden
# args.
law g_tip_candidates:
  {Cli.outcome(feat(), host(), ["--sped"]) ==
    report("unexpected argument '--sped' found",
      ["a similar argument exists: '--speed'"], "feat [OPTIONS]")
    : Cli.Outcome} &
  {Cli.outcome(neg(), host(), ["--no-sfe"]) ==
    report("unexpected argument '--no-sfe' found",
      ["a similar argument exists: '--no-safe'"], "neg [OPTIONS]")
    : Cli.Outcome} &
  {Cli.outcome(feat(), host(), ["--secrt"]) ==
    report("unexpected argument '--secrt' found", [], "feat [OPTIONS]")
    : Cli.Outcome}

# G-TIP: a candidate qualifies within max(1, n / 3) edits of optimal string
# alignment, n counting the typed name without dashes (n = 2, 3, 6); at most
# 3 are shown, by distance, then declaration order.
law g_tip_distance:
  {Cli.suggest("ab", ["ax", "xy", "abc"]) == ["ax", "abc"]
    : List<&2, String>} &
  {Cli.suggest("abc", ["abd", "axy", "ab"]) == ["abd", "ab"]
    : List<&2, String>} &
  {Cli.suggest("abc", ["bac"]) == ["bac"] : List<&2, String>} &
  {Cli.suggest("abcdef", ["abcxyz", "abcdxy", "abcdex", "bacdef"])
    == ["abcdex", "bacdef", "abcdxy"] : List<&2, String>} &
  {Cli.suggest("cat", ["bat", "cot", "cap", "car"]) == ["bat", "cot", "cap"]
    : List<&2, String>} &
  {Cli.suggest("--forse", ["--force", "--help"]) == ["--force"]
    : List<&2, String>}

def painted() -> Cli.Cmd:
  Cli.cmd("painted", "Paint test", [Cli.arg("-f, --force", "Force", [])])

def tty() -> Cli.Host:
  Cli.host_tty(host(), True{}, True{})

# G-COLOR: rule 7 colors each stream that is a TTY; Term keeps the host
# width unclamped.
law g_color_tty:
  {Cli.term(painted(), host(), [])
    == Cli.Term{False{}, False{}, 80n} : Cli.Term} &
  {Cli.term(painted(), tty(), [])
    == Cli.Term{True{}, True{}, 80n} : Cli.Term} &
  {Cli.term(painted(), Cli.host_tty(host(), True{}, False{}), [])
    == Cli.Term{True{}, False{}, 80n} : Cli.Term} &
  {Cli.term(painted(), Cli.host_tty(host(), False{}, True{}), [])
    == Cli.Term{False{}, True{}, 80n} : Cli.Term} &
  {Cli.term(painted(), Cli.host(120n), [])
    == Cli.Term{False{}, False{}, 120n} : Cli.Term} &
  {Cli.term(painted(), Cli.host(20n), [])
    == Cli.Term{False{}, False{}, 20n} : Cli.Term}

def env_colors(h: Cli.Host) -> (Bool & Bool):
  colors(Cli.term(painted(), h, []))

# G-COLOR: rules 3-6 apply in order; an empty variable counts as unset.
law g_color_env:
  {env_colors(Cli.host_var(tty(), "NO_COLOR", "1"))
    == (False{}, False{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(tty(), "NO_COLOR", ""))
    == (True{}, True{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(Cli.host_var(host(), "CLICOLOR_FORCE", "1"),
    "NO_COLOR", "1")) == (False{}, False{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(host(), "CLICOLOR_FORCE", "1"))
    == (True{}, True{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(host(), "CLICOLOR_FORCE", "0"))
    == (False{}, False{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(tty(), "CLICOLOR_FORCE", "0"))
    == (True{}, True{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(host(), "CLICOLOR_FORCE", ""))
    == (False{}, False{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(Cli.host_var(host(), "CLICOLOR", "0"),
    "CLICOLOR_FORCE", "1")) == (True{}, True{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(Cli.host_var(host(), "TERM", "dumb"),
    "CLICOLOR_FORCE", "1")) == (True{}, True{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(tty(), "CLICOLOR", "0"))
    == (False{}, False{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(tty(), "CLICOLOR", "1"))
    == (True{}, True{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(tty(), "TERM", "dumb"))
    == (False{}, False{}) : (Bool & Bool)} &
  {env_colors(Cli.host_var(tty(), "TERM", "xterm"))
    == (True{}, True{}) : (Bool & Bool)}

def pkg_colors(h: Cli.Host, argv: List<&2, String>) -> (Bool & Bool):
  colors(Cli.term(Demo.cli(), h, argv))

# G-COLOR: with color(), the last --color before `--` beats the environment,
# after a subcommand too; auto, an invalid value, or one after `--` falls
# through. Without color(), --color is ignored.
law g_color_flag:
  {pkg_colors(Cli.host_var(tty(), "NO_COLOR", "1"), ["--color=always"])
    == (True{}, True{}) : (Bool & Bool)} &
  {pkg_colors(tty(), ["--color", "never"])
    == (False{}, False{}) : (Bool & Bool)} &
  {pkg_colors(Cli.host_var(host(), "CLICOLOR_FORCE", "1"), ["--color=never"])
    == (False{}, False{}) : (Bool & Bool)} &
  {pkg_colors(host(), ["--color=always", "--color=never"])
    == (False{}, False{}) : (Bool & Bool)} &
  {pkg_colors(host(), ["--color=never", "add", "--color", "always"])
    == (True{}, True{}) : (Bool & Bool)} &
  {pkg_colors(tty(), ["--color=auto"])
    == (True{}, True{}) : (Bool & Bool)} &
  {pkg_colors(tty(), ["--color=never", "--color=sometimes"])
    == (True{}, True{}) : (Bool & Bool)} &
  {pkg_colors(host(), ["run", "s", "--", "--color=always"])
    == (False{}, False{}) : (Bool & Bool)} &
  {colors(Cli.term(painted(), host(), ["--color=always"]))
    == (False{}, False{}) : (Bool & Bool)}

def need() -> Cli.Cmd:
  Cli.cmd("need", "Need test", [Cli.arg("<X>", "Input", [])])

def painted_page() -> String:
  page([
    "Paint test",
    "",
    "\u{1B}[1;4mUsage:\u{1B}[0m \u{1B}[1mpainted\u{1B}[0m [OPTIONS]",
    "",
    "\u{1B}[1;4mOptions:\u{1B}[0m",
    "  \u{1B}[1m-f\u{1B}[0m, \u{1B}[1m--force\u{1B}[0m  Force",
    "  \u{1B}[1m-h\u{1B}[0m, \u{1B}[1m--help\u{1B}[0m   Print help",
  ])

# G-COLOR: help paints in the decision for its stream: titles and Usage: in
# bold underline, the command path and option names in bold; placeholders,
# separators and descriptions stay plain. help uses the stdout decision.
law g_color_help:
  {Cli.outcome(painted(), Cli.host_tty(host(), True{}, False{}), ["-h"])
    == Cli.Shown{0, painted_page(), ""} : Cli.Outcome} &
  {Cli.help(painted(), [], False{}, Cli.host_tty(host(), True{}, False{}))
    == painted_page() : String} &
  {Cli.outcome(painted(), Cli.host_tty(host(), False{}, True{}), ["-h"])
    == Cli.Shown{0, page([
    "Paint test",
    "",
    "Usage: painted [OPTIONS]",
    "",
    "Options:",
    "  -f, --force  Force",
    "  -h, --help   Print help",
  ]), ""} : Cli.Outcome} &
  {Cli.outcome(need(), Cli.host_tty(host(), False{}, True{}), [])
    == Cli.Shown{2, "", page([
    "Need test",
    "",
    "\u{1B}[1;4mUsage:\u{1B}[0m \u{1B}[1mneed\u{1B}[0m <X>",
    "",
    "\u{1B}[1;4mArguments:\u{1B}[0m",
    "  <X>         Input",
    "",
    "\u{1B}[1;4mOptions:\u{1B}[0m",
    "  \u{1B}[1m-h\u{1B}[0m, \u{1B}[1m--help\u{1B}[0m  Print help",
  ])} : Cli.Outcome}

# G-COLOR: an error paints in the stderr decision: error: in bold red, the
# user's token in yellow, tip: in bold green, a suggestion in green, and the
# usage and '--help' as in help.
law g_color_error:
  {Cli.outcome(painted(), Cli.host_tty(host(), False{}, True{}), ["--forse"])
    == Cli.Shown{2, "", page([
    "\u{1B}[1;31merror:\u{1B}[0m unexpected argument '\u{1B}[33m--forse\u{1B}[0m' found",
    "",
    "  \u{1B}[1;32mtip:\u{1B}[0m a similar argument exists: '\u{1B}[32m--force\u{1B}[0m'",
    "",
    "\u{1B}[1;4mUsage:\u{1B}[0m \u{1B}[1mpainted\u{1B}[0m [OPTIONS]",
    "",
    "For more information, try '\u{1B}[1m--help\u{1B}[0m'.",
  ])} : Cli.Outcome} &
  {Cli.outcome(painted(), Cli.host_tty(host(), True{}, False{}), ["--forse"])
    == report("unexpected argument '--forse' found",
      ["a similar argument exists: '--force'"], "painted [OPTIONS]")
    : Cli.Outcome}

# G-LINT: each problem is one line, indented 2, led by the command path.
# A BadUsage column is shown counting from 1.
law g_lint_lines:
  {Cli.problem_line(Cli.BadUsage{"tool", "--quiet.", 7n})
    == "  tool: usage '--quiet.' is invalid at column 8" : String} &
  {Cli.problem_line(Cli.BadName{"tool", "bad name"})
    == "  tool: 'bad name' is not a valid name" : String} &
  {Cli.problem_line(Cli.Dup{"tool run", "-v"})
    == "  tool run: '-v' is declared more than once" : String} &
  {Cli.problem_line(Cli.Reserved{"tool", "--help"})
    == "  tool: '--help' is reserved" : String} &
  {Cli.problem_line(Cli.Misplaced{"tool", "global"})
    == "  tool: 'global' is not allowed here" : String} &
  {Cli.problem_line(Cli.NoHelp{"tool", "-o, --output <FILE>"})
    == "  tool: '-o, --output <FILE>' has no help text" : String} &
  {Cli.problem_line(Cli.BadDefault{"tool", "count", "nope"})
    == "  tool: 'count' cannot have the default 'nope'" : String} &
  {Cli.problem_line(Cli.BadRef{"tool", "missing"})
    == "  tool: 'missing' is an unknown id or an unused or empty group"
    : String} &
  {Cli.problem_line(Cli.BadPositional{"tool", "b",
    "required positional follows an optional positional"})
    == "  tool: positional 'b': required positional follows an optional positional"
    : String} &
  {Cli.problem_line(Cli.Mixed{"tool"})
    == "  tool: has both positionals and subcommands" : String} &
  {Cli.problem_line(Cli.BadChoices{"tool", "mode"})
    == "  tool: one_of for 'mode' is empty or repeats a value" : String} &
  {Cli.problem_line(Cli.NeedBare{"tool", "color"})
    == "  tool: 'color' needs [=<V>] and bare() together, with no short"
    : String} &
  {Cli.problem_line(Cli.DecodeBug{"tool",
    "'nope' is not an argument of 'tool'"})
    == "  tool: decoder bug: 'nope' is not an argument of 'tool'" : String}

# G-LINT: a default on a flag or count is Misplaced, and also a BadDefault
# when its value is not a bool or a nat.
law g_lint_flag_default:
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.arg("--quiet", "Quiet output", [Cli.default("x")]),
  ])) == [Cli.Misplaced{"tool", "default"},
    Cli.BadDefault{"tool", "quiet", "x"}] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.arg("--quiet", "Quiet output", [Cli.default("true")]),
  ])) == [Cli.Misplaced{"tool", "default"}] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.arg("-v...", "Verbosity", [Cli.default("x")]),
  ])) == [Cli.Misplaced{"tool", "default"},
    Cli.BadDefault{"tool", "v", "x"}] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.arg("-v...", "Verbosity", [Cli.default("2")]),
  ])) == [Cli.Misplaced{"tool", "default"}] : List<&2, Cli.Problem>}
