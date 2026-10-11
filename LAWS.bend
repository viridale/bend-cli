# Purpose: laws for the pure CLI library and pkg demo.
# Expected output: ALL PROOFS CHECK.
# Run: bend PROOF.bend --verdict
# Scope: P13 bounds visible line widths; P14 preserves words in order. Neither
# pins whitespace normalization; G-TEXT pins representative wrapped content.

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
# T1-T3 text is pinned with Step output in M5.
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
