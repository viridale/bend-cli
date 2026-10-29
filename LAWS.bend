# Purpose: laws for the pure CLI library and pkg demo.
# Expected output: ALL PROOFS CHECK.
# Run: bend PROOF.bend --verdict
# Scope: P13 bounds visible line widths; P14 preserves words in order. Neither
# pins whitespace normalization; G-TEXT pins representative wrapped content.
# P12 fixes when readers, choose and route raise their own validation Bug,
# not what they return; G-READ fixes values, except a given f32 (K8), and
# what route's selected callback returns. P7 and P8 fix term's colors;
# G-HELP, G-ERR, G-TIP and G-COLOR fix outcome's bytes for V1-V5. P10 and
# P11 fix eval's codes and streams for every decoder through eval_with,
# which eval calls (eval_bridge), with usage errors at the spec's
# usage_code; P24 makes that code 1 to 255, and 2 unless the root sets
# usage_status. The M5 goldens fix eval's bytes and Go values for chosen
# cases. P16 makes eval_linted on the Linted that linted
# returns answer as eval does, P17 fixes its success and failure answers, and
# p10_linted and p11_linted carry P10 and P11 to eval_linted on every
# Linted (eval_linted_bridge). P18 fixes the first-match lookups (field_find,
# find_by_key, find_sub, find_arg_info, same_text) against references that
# walk the whole list with String.eq, P19 fixes the scanner's compiled scopes
# against those raw lookups and verdict's arg against the scope the scan
# reaches, and P20 fixes which route keys name a command against cutting the
# key into words, and route's whole answer against references that walk its
# table. P21 fixes that a reader whose verdict passes reads only values the
# parse or the samples check runs validated, on any argv of a lint-clean
# command; which values a type accepts is G-VAL's. G-CHECK fixes which
# states of an arg the samples try; no law says a decoder's Bug on a parse
# shows on some sample, since a read may need two args out of the sample's
# state, or a value no state gives. P22 fixes that valid_nat and valid_u32
# accept exactly what Nat.read and U32.read read, so those readers never
# fall back to 0; F32.read does not reduce in the checker (K8), so the f32
# end-to-end cases cover it. P22 also fixes that choose's verdict passes only
# a table whose keys are its arg's values. P3-P6 and P15 fix the quoters
# against models of how each shell and man(7) read text; G-COMP and G-MAN fix
# the bytes of script and roff, and g_eval_builtins fixes V6. P23 makes
# arg_bytes map each char on its own; G-BYTES fixes arg_text and arg_bytes
# at UTF-8's boundaries and at each escape, their round trip on bytes that
# mix them, and parse on decoded arguments. No law states that round trip
# for every byte list. Nothing here fixes what a real shell offers from a
# script, nor Run.main's IO, which tests/e2e.bend covers (K4).

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

# G-TEXT: an emoji sequence is one wide cell, as Rust's unicode-width 0.2
# counts it: a pictograph that a ZWJ joins, a skin tone after a base that
# takes one, and tag characters add nothing; VS16 widens a narrow emoji to 2.
law g_text_width_emoji:
  {Cli.width("\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}") == 2n : Nat} &
  {Cli.width("\u{1F469}\u{1F3FD}\u{200D}\u{1F4BB}") == 2n : Nat} &
  {Cli.width("\u{1F3F3}\u{FE0F}\u{200D}\u{1F308}") == 2n : Nat} &
  {Cli.width("\u{1F441}\u{FE0F}\u{200D}\u{1F5E8}\u{FE0F}") == 2n : Nat} &
  {Cli.width("\u{2764}\u{FE0F}\u{200D}\u{1F525}") == 2n : Nat} &
  {Cli.width("\u{1F469}\u{1F3FD}\u{200D}\u{1F91D}\u{200D}\u{1F468}\u{1F3FF}")
    == 2n : Nat} &
  {Cli.width("\u{1F468}\u{200D}\u{1F469}\u{1F3FD}") == 2n : Nat} &
  {Cli.width("\u{1F44D}\u{1F3FD}") == 2n : Nat} &
  {Cli.width("\u{261D}\u{1F3FD}") == 2n : Nat} &
  {Cli.width("\u{2764}\u{FE0F}") == 2n : Nat} &
  {Cli.width("1\u{FE0F}\u{20E3}") == 2n : Nat} &
  {Cli.width("\u{1F3F4}\u{E0067}\u{E0062}\u{E0065}\u{E006E}\u{E0067}\u{E007F}")
    == 2n : Nat} &
  {Cli.width("\u{1F1FA}\u{1F1F8}") == 2n : Nat}

# G-TEXT: outside a sequence each code point keeps its own width. A ZWJ joins
# only two pictographs, a skin tone only follows a base that takes one, and a
# later VS16 or skin tone in the same emoji adds as if alone.
law g_text_width_emoji_edges:
  {Cli.width("a\u{200D}\u{1F469}") == 3n : Nat} &
  {Cli.width("\u{1F468}\u{200D}a") == 3n : Nat} &
  {Cli.width("1\u{200D}\u{1F525}") == 3n : Nat} &
  {Cli.width("\u{1F468} \u{200D}\u{1F469}") == 5n : Nat} &
  {Cli.width("\u{1F44D}\u{200D}\u{1F3FD}") == 4n : Nat} &
  {Cli.width("a\u{1F3FD}") == 3n : Nat} &
  {Cli.width("\u{1F600}\u{1F3FD}") == 4n : Nat} &
  {Cli.width("\u{1F44D}\u{1F3FD}\u{1F3FD}") == 4n : Nat} &
  {Cli.width("\u{1F3FD}") == 2n : Nat} &
  {Cli.width("\u{1F600}\u{FE0F}") == 2n : Nat} &
  {Cli.width("a\u{FE0F}") == 1n : Nat} &
  {Cli.width("\u{2605}\u{FE0F}") == 1n : Nat} &
  {Cli.width("\u{2764}\u{FE0F}\u{FE0F}") == 2n : Nat} &
  {Cli.width("\u{2764}\u{FE0F}\u{2764}") == 3n : Nat} &
  {Cli.width("\u{1F441}") == 1n : Nat} &
  {Cli.width("\u{1F1FA}") == 1n : Nat} &
  {Cli.width("a\u{E0062}") == 1n : Nat}

# G-TEXT: wrapping counts an emoji sequence as its width.
law g_text_wrap_emoji:
  {Cli.wrap("\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467} ab", 5n)
    == "\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467} ab" : String} &
  {Cli.wrap("\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467} ab", 4n)
    == "\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}\nab" : String}

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

# G-LINT Misplaced: a command that needs a subcommand drops its own
# non-global options' values on descent, so their required() can never be
# met. It is reported with the command's own problems, once per required(),
# and a flag's required() only once; global(), sub_optional() and external()
# keep it.
def parent_required(attrs: List<&2, Cli.Item>,
    items: List<&2, Cli.Item>) -> Cli.Cmd:
  Cli.cmd("tool", "Tool description", List.append(&2, Cli.Item, [
    Cli.arg("--out <X>", "Output", attrs),
    Cli.sub("run", "Run it", []),
  ], items))

law g_lint_required_sub:
  {Cli.problems(parent_required([Cli.required()], []))
    == [Cli.Misplaced{"tool", "required"}] : List<&2, Cli.Problem>} &
  {Cli.problems(parent_required([Cli.required(), Cli.required()], []))
    == [Cli.Misplaced{"tool", "required"}, Cli.Misplaced{"tool", "required"}]
    : List<&2, Cli.Problem>} &
  {Cli.problems(parent_required([Cli.required(), Cli.global()], []))
    == [] : List<&2, Cli.Problem>} &
  {Cli.problems(parent_required([Cli.required()], [Cli.sub_optional()]))
    == [] : List<&2, Cli.Problem>} &
  {Cli.problems(parent_required([Cli.required()], [Cli.external()]))
    == [] : List<&2, Cli.Problem>} &
  {Cli.problems(parent_required([], [
    Cli.arg("--a <A>", "", [Cli.required()]),
    Cli.arg("--quiet", "Quiet", [Cli.required()]),
  ])) == [
    Cli.Misplaced{"tool", "required"},
    Cli.NoHelp{"tool", "--a <A>"},
    Cli.Misplaced{"tool", "required"},
  ] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.sub("remote", "Remotes", [
      Cli.arg("--name <N>", "Name", [Cli.required()]),
      Cli.sub("add", "Add one", [
        Cli.arg("--url <U>", "URL", [Cli.required()]),
      ]),
    ]),
  ])) == [Cli.Misplaced{"tool remote", "required"}] : List<&2, Cli.Problem>}

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

# G-LINT BadChoice: each one_of value must pass the arg's value type, which
# parse checks before the choices, so a choice that fails could never be
# given; lint names the first, whatever the order of the attributes. Untyped
# and file choices take any text.
law g_lint_bad_choice:
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--n <N>", "Count",
      [Cli.as_u32(), Cli.one_of(["1", "4294967296", "x"])]),
  ])) == [Cli.BadChoice{"tool", "n", "4294967296"}]
    : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--n <N>", "Count",
      [Cli.one_of(["0", "4294967295", "y"]), Cli.as_u32()]),
  ])) == [Cli.BadChoice{"tool", "n", "y"}] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool description", [
    Cli.arg("--mode <M>", "Mode", [Cli.one_of(["", "x"])]),
    Cli.arg("--path <P>", "Path", [Cli.as_file(), Cli.one_of(["-"])]),
    Cli.arg("<N>", "Level", [Cli.as_nat(), Cli.one_of(["0", "7"])]),
  ])) == [] : List<&2, Cli.Problem>} &
  {Cli.problem_line(Cli.BadChoice{"tool", "n", "x"})
    == "  tool: 'n' cannot have the choice 'x'" : String}

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

def alias_option() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--[no-]color", "Use color", [Cli.alias("--colour")]),
    Cli.arg("-o, --out <FILE>", "Output", [Cli.alias("--output")]),
  ])

# G-LEX: an alias names its arg, taking a value as the long does and setting
# a negatable arg as its long does; --no- still negates it.
law g_lex_alias:
  {Cli.scan(alias_option(), ["--output=a", "--colour", "--no-color"]) ==
    root([
      Cli.ValueHit{"out", "a"}, Cli.FlagHit{"color", True{}},
      Cli.FlagHit{"color", False{}},
    ], False{}, None{}) : Cli.ScanTrace}

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

def dash_operands() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-v", "Verbose", []),
    Cli.arg("<X>...", "Operands", [Cli.hyphen()]),
  ])

def f32_operands() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("<N>...", "Numbers", [Cli.as_f32()]),
  ])

# G-POS: a variadic slot's later values take hyphen() and as_f32() as its
# first does; an option the scope knows stays an option, and an f32 slot
# takes no other dash token.
law g_pos_variadic_dash:
  {Cli.parse(dash_operands(), host(), ["a", "-x", "-v", "-y"]) == ok([
    field("v", ["true"], Cli.Argv{}),
    field("x", ["a", "-x", "-y"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(f32_operands(), host(), ["1", "-5", "-6.5"]) == ok([
    field("n", ["1", "-5", "-6.5"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(f32_operands(), host(), ["1", "-5", "-x"]) ==
    Cli.Rejected{[], Cli.E01{"-x"}} : Cli.ParseResult}

# G-POS: a hyphen() slot takes a long token that names no option in scope,
# with or without "=", as it takes a short one; --help is still help.
law g_pos_hyphen_long:
  {Cli.parse(dash_operands(), host(), ["--x=1", "-v", "--y"]) == ok([
    field("v", ["true"], Cli.Argv{}),
    field("x", ["--x=1", "--y"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(dash_operands(), host(), ["a", "--help"]) ==
    Cli.HelpRequested{[], True{}} : Cli.ParseResult}

# A -v flag, <COMMAND>, and [ARGS]... with rest().
def retry() -> Cli.Cmd:
  Cli.cmd("retry", "Retry a command", [
    Cli.arg("-v, --verbose", "Verbose", []),
    Cli.arg("<COMMAND>", "Command", []),
    Cli.arg("[ARGS]...", "Arguments", [Cli.rest()]),
  ])

# G-POS: a rest() slot's first value may start with "-", as a hyphen()
# slot's may: a short or long token that names no option in scope, and
# every later token is a value too. An option the scope knows, by its name
# before "=", and a built-in stay options, and the slot before rest() takes
# no dash token.
law g_pos_rest_dash:
  {Cli.parse(retry(), host(), ["curl", "-fsS", "-v", "url"]) == ok([
    field("command", ["curl"], Cli.Argv{}),
    field("args", ["-fsS", "-v", "url"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(retry(), host(), ["curl", "--max-time=5", "--", "url"]) == ok([
    field("command", ["curl"], Cli.Argv{}),
    field("args", ["--max-time=5", "--", "url"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(retry(), host(), ["curl", "-v", "-x"]) == ok([
    field("verbose", ["true"], Cli.Argv{}),
    field("command", ["curl"], Cli.Argv{}),
    field("args", ["-x"], Cli.Argv{}),
  ]) : Cli.ParseResult} &
  {Cli.parse(retry(), host(), ["curl", "--verbose=1"]) ==
    Cli.Rejected{[], Cli.E05{"--verbose", "1"}} : Cli.ParseResult} &
  {Cli.parse(retry(), host(), ["curl", "--help"]) ==
    Cli.HelpRequested{[], True{}} : Cli.ParseResult} &
  {Cli.parse(retry(), host(), ["-x", "curl"]) ==
    Cli.Rejected{[], Cli.E01{"-x"}} : Cli.ParseResult}

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

def deep_tool() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-g, --global", "Root global", [Cli.global()]),
    Cli.sub("alpha", "Alpha", [
      Cli.arg("-m, --mid", "Alpha global", [Cli.global()]),
      Cli.arg("--child", "Alpha only", []),
      Cli.sub("beta", "Beta", [
        Cli.arg("--leaf", "Beta only", []),
      ]),
    ]),
  ])

# G-SUB: the globals of every ancestor reach a grandchild, the parent's
# before the root's in its fields; an ancestor's other args do not.
law g_sub_deep_globals:
  {Cli.parse(deep_tool(), host(), ["alpha", "beta", "--leaf", "-g", "-m"]) ==
    Cli.Accepted{["alpha", "beta"], [
      field("mid", ["true"], Cli.Argv{}),
      field("global", ["true"], Cli.Argv{}),
      field("leaf", ["true"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult} &
  {Cli.parse(deep_tool(), host(), ["alpha", "beta", "--child"]) ==
    Cli.Rejected{["alpha", "beta"], Cli.E01{"--child"}} : Cli.ParseResult}

def own_tool() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--out <O>", "Root output", []),
    Cli.arg("-v, --verbose...", "Root verbosity", []),
    Cli.sub("run", "Run", [
      Cli.sub_optional(),
      Cli.arg("--out <N>", "Run output", [Cli.as_nat(), Cli.global()]),
      Cli.arg("-v, --verbose", "Run verbose", []),
      Cli.sub("go", "Go", []),
    ]),
    Cli.sub("need", "Need", [
      Cli.arg("--out <O>", "Need output", [Cli.required()]),
    ]),
  ])

# G-SUB: an arg reads only occurrences scanned where it is in scope. An
# ancestor's non-global arg with the same id, given before the descent,
# neither fills it nor satisfies its required(); a global still collects
# occurrences from every scope below the one declaring it.
law g_sub_own_ids:
  {Cli.parse(own_tool(), host(), ["--out", "abc", "-vv", "run"]) ==
    Cli.Accepted{["run"], [], None{}} : Cli.ParseResult} &
  {Cli.parse(own_tool(), host(), ["--out", "abc", "run", "--out", "5",
      "-v"]) ==
    Cli.Accepted{["run"], [
      field("out", ["5"], Cli.Argv{}),
      field("verbose", ["true"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult} &
  {Cli.parse(own_tool(), host(), ["--out", "abc", "run", "go"]) ==
    Cli.Accepted{["run", "go"], [], None{}} : Cli.ParseResult} &
  {Cli.parse(own_tool(), host(), ["run", "--out", "5", "go"]) ==
    Cli.Accepted{["run", "go"], [
      field("out", ["5"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult} &
  {Cli.parse(own_tool(), host(), ["--out", "x", "need"]) ==
    Cli.Rejected{["need"], Cli.E06{["--out <O>"]}} : Cli.ParseResult}

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

def digit_tool() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-1, --one", "One per line", [Cli.global()]),
    Cli.sub("move", "Move", [
      Cli.arg("--by <N>", "Offset", [Cli.as_f32()]),
      Cli.arg("[X]", "Start", [Cli.as_f32()]),
    ]),
  ])

# G-SUB: a digit short inherited from an ancestor is in scope, so a negative
# number neither fills an as_f32 option (R6) nor an as_f32 slot (R3); an
# attached value still does.
law g_sub_digit_global:
  {Cli.parse(digit_tool(), host(), ["move", "--by", "-5"]) ==
    Cli.Rejected{["move"], Cli.E03{"--by <N>"}} : Cli.ParseResult} &
  {Cli.parse(digit_tool(), host(), ["move", "-5"]) ==
    Cli.Rejected{["move"], Cli.E01{"-5"}} : Cli.ParseResult} &
  {Cli.parse(digit_tool(), host(), ["move", "-1", "--by=-5"]) ==
    Cli.Accepted{["move"], [
      field("one", ["true"], Cli.Argv{}),
      field("by", ["-5"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult}

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

# A -v flag, and [FILES]... with delim(',') and attrs.
def delim_files(attrs: List<&2, Cli.Item>) -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("-v, --verbose", "Verbose", []),
    Cli.arg("[FILES]...", "Files", Cli.delim(',') <> attrs),
  ])

# G-VAL: delim splits every value a variadic positional takes: after "--",
# where a token that starts with "-" is an operand, and inside rest(), where
# "--" and an option the scope knows are values once the slot has its first.
# Empty pieces stay.
law g_val_delim_operands:
  {Cli.parse(delim_files([]), host(), ["x,y", "-v", "--", "-v,a", "b,c"]) ==
    ok([
      field("verbose", ["true"], Cli.Argv{}),
      field("files", ["x", "y", "-v", "a", "b", "c"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(delim_files([Cli.rest()]), host(),
    ["a,b", "-v,x", "--", "c,d", "-v"]) == ok([
      field("files", ["a", "b", "-v", "x", "--", "c", "d", "-v"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(delim_files([]), host(), ["--", ",a,,"]) == ok([
      field("files", ["", "a", "", ""], Cli.Argv{}),
    ]) : Cli.ParseResult}

# G-BYTES: arg_text decodes UTF-8 at every length, at both ends of each
# lead byte's range and next to the surrogates.
law g_bytes_utf8:
  {Cli.arg_text([104, 195, 169, 226, 130, 172, 240, 159, 152, 128]) ==
    "h\u{E9}\u{20AC}\u{1F600}" : String} &
  {Cli.arg_text([127, 194, 128, 223, 191, 224, 160, 128, 237, 159, 191,
    238, 128, 128, 239, 191, 191]) ==
    "\u{7F}\u{80}\u{7FF}\u{800}\u{D7FF}\u{E000}\u{FFFF}" : String} &
  {Cli.arg_text([240, 144, 128, 128, 243, 191, 191, 191, 244, 143, 191,
    191]) == "\u{10000}\u{FFFFF}\u{10FFFF}" : String} &
  {Cli.arg_text([]) == "" : String}

# G-BYTES: a byte that starts no well-formed UTF-8 sequence becomes U+DC00
# plus the byte (PEP 383), and decoding resumes at the next byte: a Latin-1
# name, lone continuation bytes, the lead bytes UTF-8 never uses, overlong
# forms, surrogates' forms (an escape's own included), code points past
# U+10FFFF, and sequences cut short by the end or by a byte that does not
# continue them. A value past 255 is no byte and becomes U+FFFD, even where
# its low byte would lead or continue a sequence.
law g_bytes_escape:
  {Cli.arg_text([99, 97, 102, 233]) == "caf\u{DCE9}" : String} &
  {Cli.arg_text([128, 191]) == "\u{DC80}\u{DCBF}" : String} &
  {Cli.arg_text([192, 128, 193, 191, 245, 255]) ==
    "\u{DCC0}\u{DC80}\u{DCC1}\u{DCBF}\u{DCF5}\u{DCFF}" : String} &
  {Cli.arg_text([224, 159, 191, 240, 143, 191, 191]) ==
    "\u{DCE0}\u{DC9F}\u{DCBF}\u{DCF0}\u{DC8F}\u{DCBF}\u{DCBF}" : String} &
  {Cli.arg_text([237, 160, 128, 237, 179, 169]) ==
    "\u{DCED}\u{DCA0}\u{DC80}\u{DCED}\u{DCB3}\u{DCA9}" : String} &
  {Cli.arg_text([244, 144, 128, 128]) ==
    "\u{DCF4}\u{DC90}\u{DC80}\u{DC80}" : String} &
  {Cli.arg_text([226, 130, 65, 194, 127, 194, 192, 240, 159, 152]) ==
    "\u{DCE2}\u{DC82}A\u{DCC2}\u{7F}\u{DCC2}\u{DCC0}\u{DCF0}\u{DC9F}\u{DC98}"
    : String} &
  {Cli.arg_text([256, 65, 195, 425, 451, 169]) ==
    "\u{FFFD}A\u{DCC3}\u{FFFD}\u{FFFD}\u{DCA9}" : String}

# G-BYTES: arg_bytes writes each of U+DC80..U+DCFF as the byte it escapes,
# and every other Unicode scalar as UTF-8, at every length's ends. The
# surrogates outside that range and the chars past U+10FFFF are no scalar,
# and become U+FFFD's bytes, as Bend's writer prints them.
law g_bytes_out:
  {Cli.arg_bytes("h\u{E9}\u{20AC}\u{1F600}") ==
    [104, 195, 169, 226, 130, 172, 240, 159, 152, 128] : List<&2, U32>} &
  {Cli.arg_bytes("\u{7F}\u{80}\u{7FF}\u{800}\u{FFFF}\u{10000}\u{10FFFF}") ==
    [127, 194, 128, 223, 191, 224, 160, 128, 239, 191, 191, 240, 144, 128,
      128, 244, 143, 191, 191] : List<&2, U32>} &
  {Cli.arg_bytes("caf\u{DCE9}\u{DC80}\u{DCFF}") ==
    [99, 97, 102, 233, 128, 255] : List<&2, U32>} &
  {Cli.arg_bytes("\u{D7FF}\u{D800}\u{DC7F}\u{DD00}\u{DFFF}\u{E000}") ==
    [237, 159, 191, 239, 191, 189, 239, 191, 189, 239, 191, 189, 239, 191,
      189, 238, 128, 128] : List<&2, U32>} &
  {Cli.arg_bytes(SCon{Char.from_u32(1114112), SNil{}}) ==
    [239, 191, 189] : List<&2, U32>} &
  {Cli.arg_bytes("") == [] : List<&2, U32>}

# Bytes that mix every way arg_text escapes with UTF-8 it decodes.
def mixed_bytes() -> List<&2, U32>:
  [99, 97, 102, 233, 195, 169, 237, 179, 169, 226, 130, 65, 192, 128, 244,
    144, 128, 128, 240, 159, 152, 128, 237, 160, 128, 128, 255]

# G-BYTES: arg_bytes gives back the bytes arg_text decoded.
law g_bytes_round:
  {Cli.arg_bytes(Cli.arg_text(mixed_bytes())) == mixed_bytes()
    : List<&2, U32>}

# P23: arg_bytes maps each char on its own, so the bytes of a value parse
# cuts from an argument (after "--name=", or a delim piece) are that
# part's bytes of the argument.
law p23:
  for a: String
  for b: String
  {Cli.arg_bytes(String.append(a, b)) ==
    List.append(&2, U32, Cli.arg_bytes(a), Cli.arg_bytes(b))
    : List<&2, U32>}

# "--value=" and "--n=" as bytes.
def value_eq() -> List<&2, U32>:
  [45, 45, 118, 97, 108, 117, 101, 61]

def n_eq() -> List<&2, U32>:
  [45, 45, 110, 61]

# G-BYTES: parse keeps a decoded argument's escapes in the value it cuts,
# attached, in the next argument, or as a delim piece, and E04 quotes the
# value with them.
law g_bytes_parse:
  {Cli.parse(typed([]), host(), [Cli.arg_text(List.append(&2, U32,
    value_eq(), [99, 97, 102, 233]))]) == ok([
      field("value", ["caf\u{DCE9}"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(typed([]), host(),
    ["--value", Cli.arg_text([99, 97, 102, 233])]) == ok([
      field("value", ["caf\u{DCE9}"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(numbers([Cli.delim(',')]), host(), [Cli.arg_text(
    List.append(&2, U32, n_eq(), [99, 97, 102, 233, 44, 255]))]) == ok([
      field("n", ["caf\u{DCE9}", "\u{DCFF}"], Cli.Argv{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(typed([Cli.as_u32()]), host(), [Cli.arg_text(List.append(&2,
    U32, value_eq(), [52, 255]))]) ==
    Cli.Rejected{[], Cli.E04{"--value <V>", "4\u{DCFF}",
      "expected a whole number from 0 to 4294967295"}}
    : Cli.ParseResult}

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

# §8.6: an arg may name several variables; the first that is set and not
# empty supplies it, and a later one is never read.
def env_chain() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--out <X>", "Output", [
      Cli.env("TOOL_OUT"), Cli.env("LEGACY_OUT"), Cli.default("d")]),
    Cli.arg("--n <N>", "Count", [
      Cli.as_nat(), Cli.env("TOOL_N"), Cli.env("LEGACY_N")]),
  ])

# G-SRC: the first variable that is set and not empty wins, after argv and
# before the default; an invalid value is E11 with that variable's name.
law g_src_env_names:
  {Cli.parse(env_chain(),
    Cli.host_var(Cli.host_var(host(), "TOOL_OUT", "new"), "LEGACY_OUT", "old"),
    []) == ok([field("out", ["new"], Cli.Env{})]) : Cli.ParseResult} &
  {Cli.parse(env_chain(), Cli.host_var(host(), "LEGACY_OUT", "old"), []) ==
    ok([field("out", ["old"], Cli.Env{})]) : Cli.ParseResult} &
  {Cli.parse(env_chain(),
    Cli.host_var(Cli.host_var(host(), "TOOL_OUT", ""), "LEGACY_OUT", "old"),
    []) == ok([field("out", ["old"], Cli.Env{})]) : Cli.ParseResult} &
  {Cli.parse(env_chain(), Cli.host_var(host(), "LEGACY_OUT", ""), []) ==
    ok([field("out", ["d"], Cli.Default{})]) : Cli.ParseResult} &
  {Cli.parse(env_chain(), Cli.host_var(host(), "LEGACY_OUT", "old"),
    ["--out", "argv"]) == ok([field("out", ["argv"], Cli.Argv{})])
    : Cli.ParseResult} &
  {Cli.parse(env_chain(),
    Cli.host_var(Cli.host_var(host(), "TOOL_N", "7"), "LEGACY_N", "nope"),
    []) == ok([
      field("out", ["d"], Cli.Default{}),
      field("n", ["7"], Cli.Env{}),
    ]) : Cli.ParseResult} &
  {Cli.parse(env_chain(),
    Cli.host_var(Cli.host_var(host(), "TOOL_N", "nope"), "LEGACY_N", "5"),
    []) == Cli.Rejected{[], Cli.E11{"--n <N>", "nope", "TOOL_N",
      "expected a whole number from 0 to 281474976710655"}}
    : Cli.ParseResult} &
  {Cli.parse(env_chain(), Cli.host_var(host(), "LEGACY_N", "nope"), []) ==
    Cli.Rejected{[], Cli.E11{"--n <N>", "nope", "LEGACY_N",
      "expected a whole number from 0 to 281474976710655"}}
    : Cli.ParseResult}

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

# Global --json and --yaml form fmt, which the root makes exclusive and needs
# one of before it declares the global --out. run and deep below it declare
# no rules; conv adds --toml to fmt and needs one of fmt itself.
def fmt_tool() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--json", "JSON output", [Cli.global(), Cli.group("fmt")]),
    Cli.arg("--yaml", "YAML output", [Cli.global(), Cli.group("fmt")]),
    Cli.exclusive("fmt"),
    Cli.need_one("fmt"),
    Cli.arg("--out <X>", "Output", [Cli.global(), Cli.required()]),
    Cli.sub("run", "Run it", [
      Cli.sub("deep", "Go deeper", []),
      Cli.sub_optional(),
    ]),
    Cli.sub("conv", "Convert", [
      Cli.arg("--toml", "TOML output", [Cli.group("fmt")]),
      Cli.need_one("fmt"),
    ]),
    Cli.sub_optional(),
  ])

# G-REL: a command's exclusive(g) and need_one(g) hold in every subcommand
# below it when every arg the command puts in g is global(), over g's
# members in that subcommand's scope, as E06 and E07 report them there. E06
# lists what the command passes down in the order the command declares it,
# before the subcommand's own items, and a group once.
law g_rel_global_groups:
  {Cli.parse(fmt_tool(), host(), ["--out", "x", "--json", "--yaml", "run"]) ==
    Cli.Rejected{["run"], Cli.E07{"--yaml", "--json"}} : Cli.ParseResult} &
  {Cli.parse(fmt_tool(), host(), ["--out", "x", "run"]) ==
    Cli.Rejected{["run"], Cli.E06{["<--json|--yaml>"]}} : Cli.ParseResult} &
  {Cli.parse(fmt_tool(), host(), ["run", "deep"]) ==
    Cli.Rejected{["run", "deep"], Cli.E06{["<--json|--yaml>", "--out <X>"]}}
    : Cli.ParseResult} &
  {Cli.parse(fmt_tool(), host(),
    ["--json", "run", "deep", "--yaml", "--out", "x"]) ==
    Cli.Rejected{["run", "deep"], Cli.E07{"--yaml", "--json"}}
    : Cli.ParseResult} &
  {Cli.parse(fmt_tool(), host(), ["run", "--yaml", "--out", "x"]) ==
    Cli.Accepted{["run"], [
      field("yaml", ["true"], Cli.Argv{}),
      field("out", ["x"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult} &
  {Cli.parse(fmt_tool(), host(), ["--out", "x", "conv"]) ==
    Cli.Rejected{["conv"], Cli.E06{["<--json|--yaml|--toml>"]}}
    : Cli.ParseResult} &
  {Cli.parse(fmt_tool(), host(), ["--out", "x", "--json", "conv", "--toml"])
    == Cli.Rejected{["conv"], Cli.E07{"--toml", "--json"}}
    : Cli.ParseResult}

# pick has only the root's own args, and run reuses the name for its own;
# mix has a global member and a local one; glob has only a global one, and
# run adds a local one and needs one of glob after pick.
def group_scopes() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
    Cli.arg("--g", "G", [Cli.global(), Cli.group("mix")]),
    Cli.arg("--l", "L", [Cli.group("mix")]),
    Cli.arg("--q", "Q", [Cli.global(), Cli.group("glob")]),
    Cli.exclusive("pick"),
    Cli.need_one("pick"),
    Cli.need_one("mix"),
    Cli.need_one("glob"),
    Cli.sub("run", "Run it", [
      Cli.arg("--c", "C", [Cli.group("pick")]),
      Cli.arg("--d", "D", [Cli.group("pick")]),
      Cli.arg("--r", "R", [Cli.group("glob")]),
      Cli.need_one("pick"),
      Cli.need_one("glob"),
    ]),
    Cli.sub("other", "Other", []),
    Cli.sub_optional(),
  ])

# G-REL: a rule stays at its command when the command puts a non-global arg
# in its group: a group of local args, even where a subcommand reuses its
# name, and a group that mixes global and local args. A carried group that a
# subcommand also needs one of stays where the command declares it.
law g_rel_global_groups_scope:
  {Cli.parse(group_scopes(), host(), ["--q", "run", "--c", "--d"]) ==
    Cli.Accepted{["run"], [
      field("q", ["true"], Cli.Argv{}),
      field("c", ["true"], Cli.Argv{}),
      field("d", ["true"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult} &
  {Cli.parse(group_scopes(), host(), ["other"]) ==
    Cli.Rejected{["other"], Cli.E06{["<--q>"]}} : Cli.ParseResult} &
  {Cli.parse(group_scopes(), host(), ["run"]) ==
    Cli.Rejected{["run"], Cli.E06{["<--q|--r>", "<--c|--d>"]}}
    : Cli.ParseResult} &
  {Cli.parse(group_scopes(), host(), ["--l", "--q", "run", "--c"]) ==
    Cli.Accepted{["run"], [
      field("q", ["true"], Cli.Argv{}),
      field("c", ["true"], Cli.Argv{}),
    ], None{}} : Cli.ParseResult}

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
    bug_of(Cli.Program, Cli.program(m, id)),
    bug_of(Maybe<&2, Cli.Program>, Cli.program_opt(m, id)),
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

# retry with a nat -n, --times, a --tag list, and command declared with attrs.
def wrapper(command: String, attrs: List<&2, Cli.Item>) -> Cli.Cmd:
  Cli.cmd("retry", "Run a command until it succeeds", [
    Cli.arg("-n, --times <N>", "Tries", [Cli.as_nat(), Cli.default("3")]),
    Cli.arg("--tag <T>...", "Tags", []),
    Cli.arg(command, "Program and its arguments", attrs),
  ])

# G-CHECK: program and program_opt read a variadic string positional with
# rest(); a bare program needs it always present. The kind is checked
# first, then absence, then rest().
law g_check_program:
  {Cli.check(~Cli.Program, ~(+m => Cli.program(m, "command")),
    wrapper("<COMMAND>...", [Cli.rest()])) == [] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Program, ~(+m => Cli.program(m, "command")),
    wrapper("[COMMAND]...", [Cli.rest(), Cli.default("true")])) ==
    [] : List<&2, Cli.Problem>} &
  {Cli.check(~Maybe<&2, Cli.Program>, ~(+m => Cli.program_opt(m, "command")),
    wrapper("[COMMAND]...", [Cli.rest()])) == [] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Program, ~(+m => Cli.program(m, "command")),
    wrapper("[COMMAND]...", [Cli.rest()])) == [
    Cli.DecodeBug{"retry",
      "'command' may be absent; read it with Cli.program_opt"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Program, ~(+m => Cli.program(m, "command")),
    wrapper("<COMMAND>...", [])) == [
    Cli.DecodeBug{"retry",
      "'command' has no Cli.rest(); give it one or read it with Cli.strs"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Maybe<&2, Cli.Program>, ~(+m => Cli.program_opt(m, "command")),
    wrapper("[COMMAND]...", [])) == [
    Cli.DecodeBug{"retry",
      "'command' has no Cli.rest(); give it one or read it with Cli.strs"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Program, ~(+m => Cli.program(m, "command")),
    wrapper("[COMMAND]...", [])) == [
    Cli.DecodeBug{"retry",
      "'command' may be absent; read it with Cli.program_opt"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Program, ~(+m => Cli.program(m, "command")),
    wrapper("<COMMAND>", [])) == [
    Cli.DecodeBug{"retry",
      "'command' is a string value; read it with Cli.str"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Program, ~(+m => Cli.program(m, "command")),
    wrapper("<COMMAND>...", [Cli.as_nat(), Cli.rest()])) == [
    Cli.DecodeBug{"retry",
      "'command' is a list of nat values; read it with Cli.nats"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Cli.Program, ~(+m => Cli.program(m, "tag")),
    wrapper("<COMMAND>...", [Cli.rest()])) == [
    Cli.DecodeBug{"retry",
      "'tag' is a list of string values; read it with Cli.strs"},
  ] : List<&2, Cli.Problem>}

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

# G-CHECK: samples at each path that can complete, in pre-order, skipping the
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

def worded() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.completions(),
    Cli.sub("completions", "Namesake", []),
    Cli.sub("ab", "AB", []),
    Cli.sub("a", "A", [Cli.sub("b", "B", [])]),
    Cli.sub("a", "Namesake", []),
    Cli.sub("xy", "XY", []),
    Cli.sub("c d", "Spaced", []),
  ])

# Route's Bug at worded()'s root for a table of "" and keys, or none.
def word_bug(keys: List<&2, String>) -> Maybe<&2, String>:
  bug_of(Cli.Matches, Cli.route(Cli.Matches, Cli.sample(worded(), []),
    keep_table("" <> keys)))

# G-CHECK: a route key's words are its text cut at every space, "" giving
# none; each word is the whole name of the first subcommand so named among
# the previous word's subcommands, from the root, and that one must not be a
# built-in. So a name is not matched by a prefix, an extension, a name with
# a space, a later namesake, or a word left empty by a leading, trailing or
# doubled space.
law g_check_route_words:
  {word_bug(["ab", "a", "a b", "xy"]) == None{} : Maybe<&2, String>} &
  {word_bug(["ax"]) == Some{"route 'ax' is not a command"}
    : Maybe<&2, String>} &
  {word_bug(["x"]) == Some{"route 'x' is not a command"}
    : Maybe<&2, String>} &
  {word_bug(["c d"]) == Some{"route 'c d' is not a command"}
    : Maybe<&2, String>} &
  {word_bug(["completions"]) ==
    Some{"route 'completions' is not a command"} : Maybe<&2, String>} &
  {word_bug(["a  b"]) == Some{"route 'a  b' is not a command"}
    : Maybe<&2, String>} &
  {word_bug(["a "]) == Some{"route 'a ' is not a command"}
    : Maybe<&2, String>} &
  {word_bug([" a"]) == Some{"route ' a' is not a command"}
    : Maybe<&2, String>} &
  {word_bug(["a ab"]) == Some{"route 'a ab' is not a command"}
    : Maybe<&2, String>}

# ---- First-match lookups ----
# Each reference below walks its whole list and compares with String.eq;
# the code's walks stop at their first hit and compare with same_text.

# P18: same_text is String.eq.
law p18_text:
  for a: String
  for b: String
  {Cli.same_text(a, b) == String.eq(a, b) : Bool}

# The value under the first key equal to key, keys and values paired up to
# the shorter list.
def keyed(a, -A: Kind(a), keys: List<&2, String>, values: List<a, A>,
    +key: String) -> Maybe<a, A>:
  match keys values:
    case k <> kt v <> vt:
      Bool.pick(Maybe<a, A>, String.eq(k, key), Some{v},
        keyed(a, A, kt, vt, key))
    case _ _: None{}

# P18: find_by_key, which choose (values Data) and route (callbacks) call,
# answers keyed's value.
law p18_key:
  for -a: Quant
  for -A: Kind(a)
  for +keys: List<&2, String>
  for values: List<a, A>
  for +key: String
  {Cli.find_by_key(a, A, keys, values, key)
    == keyed(a, A, keys, values, key) : Maybe<a, A>}

# The first field whose key is id, or an absent one named id.
def field_ref(fields: List<&2, Cli.Field>, +id: String) -> Cli.Field:
  match fields:
    case Nil{}: Cli.Field{id, [], Cli.Absent{}}
    case Cli.Field{+key, values, source} <> tail:
      Bool.pick(Cli.Field, String.eq(key, id),
        Cli.Field{key, values, source}, field_ref(tail, id))

# P18: field_find, which every reader calls, answers field_ref's field.
law p18_field:
  for +fields: List<&2, Cli.Field>
  for +id: String
  {Cli.field_find(fields, id) == field_ref(fields, id) : Cli.Field}

# Whether some Alias among items is named query.
def aliases_name(items: List<&2, Cli.Item>, +query: String) -> Bool:
  match items:
    case Nil{}: False{}
    case Cli.Alias{name} <> tail:
      Bool.or(String.eq(name, query), aliases_name(tail, query))
    case head <> tail: aliases_name(tail, query)

# The first Sub named query or with an Alias named query.
def sub_ref(items: List<&2, Cli.Item>, +query: String) ->
    Maybe<&2, Cli.SubFound>:
  match items:
    case Nil{}: None{}
    case Cli.Sub{+name, about, +children} <> tail:
      Bool.pick(Maybe<&2, Cli.SubFound>,
        Bool.or(String.eq(query, name), aliases_name(children, query)),
        Some{Cli.SubFound{name, children}}, sub_ref(tail, query))
    case head <> tail: sub_ref(tail, query)

# P18: find_sub, which help, tips and verdict's scope walk call, answers
# sub_ref's subcommand.
law p18_sub:
  for +items: List<&2, Cli.Item>
  for +query: String
  {Cli.find_sub(items, query) == sub_ref(items, query)
    : Maybe<&2, Cli.SubFound>}

# The info of the first Arg whose id is id.
def arg_ref(items: List<&2, Cli.Item>, +id: String) ->
    Maybe<&2, Cli.ArgInfo>:
  match items:
    case Nil{}: None{}
    case Cli.Arg{usage, help, attrs} <> tail:
      +info = Cli.arg_info(usage, attrs)
      Bool.pick(Maybe<&2, Cli.ArgInfo>, String.eq(Cli.info_id(info), id),
        Some{info}, arg_ref(tail, id))
    case head <> tail: arg_ref(tail, id)

# P18: find_arg_info, which verdict calls, answers arg_ref's info.
law p18_arg:
  for +items: List<&2, Cli.Item>
  for +id: String
  {Cli.find_arg_info(items, id) == arg_ref(items, id)
    : Maybe<&2, Cli.ArgInfo>}

# P19: a scope the scanner compiles from items, inheriting globals, finds an
# option as find_option does on items and then on globals. So its own keys
# answer before inherited ones, which only a spec lint rejects can show.
law p19_option:
  for +items: List<&2, Cli.Item>
  for +globals: List<&2, Cli.Item>
  for path: List<&2, String>
  for +query: String
  {Cli.find_option_scope(Cli.Scope{path,
    Cli.spec_node(items, Cli.spec_items(globals))}, query)
    == Maybe.or(&2, Cli.OptFound, Cli.find_option(items, query),
      Cli.find_option(globals, query)) : Maybe<&2, Cli.OptFound>}

# P19: that scope's children inherit its own globals, then globals. With
# p19_option, a scope at any depth finds its own options first, then its
# parent's globals, and so on up to the root's.
law p19_inherit:
  for +items: List<&2, Cli.Item>
  for +globals: List<&2, Cli.Item>
  {Cli.spec_inherit(Cli.spec_node(items, Cli.spec_items(globals)))
    == Cli.spec_items(List.append(&2, Cli.Item, Cli.global_items(items),
      globals)) : List<&2, Cli.SpecItem>}

def sub_key_of(found: Maybe<&2, Cli.SubFound>) -> Maybe<&2, Cli.SubKey>:
  match found:
    case None{}: None{}
    case Some{Cli.SubFound{name, +children}}:
      Some{Cli.SubKey{name, Cli.find_aliases(children), children}}

# P19: the compiled scope finds the subcommand find_sub finds on items.
law p19_sub:
  for +items: List<&2, Cli.Item>
  for globals: List<&2, Cli.SpecItem>
  for path: List<&2, String>
  for +query: String
  {Cli.scope_find_sub(Cli.Scope{path, Cli.spec_node(items, globals)}, query)
    == sub_key_of(Cli.find_sub(items, query)) : Maybe<&2, Cli.SubKey>}

# P19: the scanner's arg lookup over parsed items, which the group, conflict
# and requires checks call, answers as find_arg_info on the raw items.
law p19_arg:
  for +items: List<&2, Cli.Item>
  for +id: String
  {Cli.find_spec_info(Cli.spec_items(items), id, None{})
    == Cli.find_arg_info(items, id) : Maybe<&2, Cli.ArgInfo>}

# P19: a compiled scope's args, which fill its fields in order and which the
# required, group, conflict and requires checks walk, are the globals it
# inherits and then its own items.
law p19_arg_order:
  for +items: List<&2, Cli.Item>
  for +globals: List<&2, Cli.SpecItem>
  for path: List<&2, String>
  {Cli.scope_arg_items(Cli.Scope{path, Cli.spec_node(items, globals)})
    == List.append(&2, Cli.SpecItem, globals, Cli.spec_items(items))
    : List<&2, Cli.SpecItem>}

# The scan's state once it enters found's subcommand, as it does for a
# subcommand token; None when no subcommand answered.
def scan_enter(found: Maybe<&2, Cli.SubKey>, state: Cli.ScanState) ->
    Maybe<&2, Cli.ScanState>:
  match found:
    case None{}: None{}
    case Some{sub}: Some{Cli.scan_descend(state, sub)}

# The scope the scan reaches from found's state by entering each name on
# path in turn; None at a name its scope has no subcommand for.
def scope_at(path: List<&2, String>, found: Maybe<&2, Cli.ScanState>) ->
    Maybe<&2, Cli.Scope>:
  match path found:
    case _ None{}: None{}
    case Nil{} Some{state}: Some{Cli.scan_state_scope(state)}
    case name <> tail Some{+state}:
      scope_at(tail,
        scan_enter(Cli.scope_find_sub(Cli.scan_state_scope(state), name),
          state))

# verdict's answer once found holds id's arg, or none: a Bug naming the
# command path, else want's check of that arg's kind and attributes.
def verdict_ref(found: Maybe<&2, Cli.ArgInfo>, id: String, name: String,
    path: List<&2, String>, want: Cli.Want) -> Maybe<&2, String>:
  match found:
    case None{}:
      Some{String.concat(["'", id, "' is not an argument of '",
        String.join(name <> path, " "), "'"])}
    case Some{Cli.ArgInfo{key, usage, short, long, kind, attrs}}:
      Cli.want_verdict(want, id, kind, attrs)

def verdict_at(scope: Maybe<&2, Cli.Scope>, +name: String, about: String,
    items: List<&2, Cli.Item>, +path: List<&2, String>, +id: String,
    +want: Cli.Want) -> Type:
  match scope:
    case None{}: Unit
    case Some{s}:
      {Cli.verdict(Cli.Cmd{name, about, items}, path, id, want)
        == verdict_ref(Cli.find_spec_info(Cli.scope_arg_items(s), id,
          None{}), id, name, path, want) : Maybe<&2, String>}

# P19: verdict, which every reader and choose call, judges id's arg in the
# scope the scan reaches at path from scan_start: the first arg there with
# that id, whose field the reader reads (p19_arg_order, p18_field). It says
# nothing at a path the scan cannot reach.
law p19_verdict:
  for +name: String
  for +about: String
  for +items: List<&2, Cli.Item>
  for +path: List<&2, String>
  for +id: String
  for +want: Cli.Want
  verdict_at(scope_at(path,
    Some{Cli.scan_start(Cli.Cmd{name, about, items})}), name, about, items,
    path, id, want)

# The children of the first Sub named name.
def named_sub(items: List<&2, Cli.Item>, +name: String) ->
    Maybe<&2, List<&2, Cli.Item>>:
  match items:
    case Nil{}: None{}
    case Cli.Sub{key, about, children} <> tail:
      Bool.pick(Maybe<&2, List<&2, Cli.Item>>, String.eq(key, name),
        Some{children}, named_sub(tail, name))
    case head <> tail: named_sub(tail, name)

# A found subcommand's children, unless it is a built-in.
def user_found(found: Maybe<&2, List<&2, Cli.Item>>) ->
    Maybe<&2, List<&2, Cli.Item>>:
  match found:
    case None{}: None{}
    case Some{+children}:
      Bool.pick(Maybe<&2, List<&2, Cli.Item>>, Cli.has_builtin(children),
        None{}, Some{children})

# Whether each word names a user subcommand of the one before, from found.
def command_words(words: List<&2, String>,
    found: Maybe<&2, List<&2, Cli.Item>>) -> Bool:
  match words found:
    case _ None{}: False{}
    case Nil{} Some{items}: True{}
    case word <> tail Some{items}:
      command_words(tail, user_found(named_sub(items, word)))

# A route key's words: none for "", else its text cut at every space.
def key_words(+key: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(key), [],
    String.split(key, ' '))

# P20: route_key, which route checks every table key with, holds exactly
# when the key's words name a command, as g_check_route_words describes.
law p20:
  for +key: String
  for +items: List<&2, Cli.Item>
  {Cli.route_key(key, items) == command_words(key_words(key), Some{items})
    : Bool}

# The callback of table's first entry keyed key.
def table_call(-A: Type, table: List<(String & Cli.Call(A))>, +key: String)
    -> Maybe<Cli.Call(A)>:
  match table:
    case Nil{}: None{}
    case entry <> tail:
      (k, call) = entry
      Bool.pick(Maybe<Cli.Call(A)>, String.eq(k, key), Some{call},
        table_call(A, tail, key))

# Table's first key whose words name no command, from items.
def table_bad(-A: Type, table: List<(String & Cli.Call(A))>,
    +items: List<&2, Cli.Item>) -> Maybe<&2, String>:
  match table:
    case Nil{}: None{}
    case entry <> tail:
      (+key, call) = entry
      Bool.pick(Maybe<&2, String>, command_words(key_words(key), Some{items}),
        table_bad(A, tail, items), Some{key})

# The found callback applied to m, unless bad names a key that names no
# command.
def bad_answer(-A: Type, bad: Maybe<&2, String>, call: Cli.Call(A),
    m: Cli.Matches) -> Cli.Dec(A):
  match bad:
    case None{}: call(m)
    case Some{key}:
      Fail{Cli.Bug{String.concat(["route '", key, "' is not a command"])}}

# route's answer from what it found: no callback for the path is a Bug at
# text, the command's path, reported before any bad key.
def route_answer(-A: Type, found: Maybe<Cli.Call(A)>,
    bad: Maybe<&2, String>, text: String, m: Cli.Matches) -> Cli.Dec(A):
  match found:
    case None{}: Fail{Cli.Bug{String.concat(["no route for '", text, "'"])}}
    case Some{call}: bad_answer(A, bad, call, m)

# P20: at the Matches of a command's path, route answers a Bug when no
# table key is the path's words joined by spaces, checked first; else a Bug
# naming the table's first key whose words name no command (p20's rule);
# else the path's first callback, applied to those same Matches.
law p20_route:
  for -A: Type
  for +name: String
  for +about: String
  for +items: List<&2, Cli.Item>
  for +path: List<&2, String>
  for +fields: List<&2, Cli.Field>
  for +external: Maybe<&2, Cli.ExternalArgs>
  for table: List<(String & Cli.Call(A))>
  {Cli.route(A, Cli.Matches{Cli.Cmd{name, about, items}, path, fields,
      external}, table)
    == route_answer(A, table_call(A, table, String.join(path, " ")),
      table_bad(A, table, items), String.join(name <> path, " "),
      Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
    : Cli.Dec(A)}

# P21: a value as the reader with stem converts it passes the check parse
# applies for that type: valid_nat, valid_u32, valid_f32 or valid_bool; a str
# reader reads any value.
def read_typed(+stem: String, +value: String) -> Bool:
  Bool.pick(Bool, String.eq(stem, "nat"), Cli.valid_nat(value),
    Bool.pick(Bool, String.eq(stem, "u32"), Cli.valid_u32(value),
      Bool.pick(Bool, String.eq(stem, "f32"), Cli.valid_f32(value),
        Bool.pick(Bool, String.eq(stem, "bool"), Cli.valid_bool(value),
          True{}))))

def read_all(values: List<&2, String>, +stem: String) -> Bool:
  match values:
    case Nil{}: True{}
    case value <> tail:
      Bool.and(read_typed(stem, value), read_all(tail, stem))

# A flag's values are "true" or "false", which flag reads with String.eq.
def read_flags(values: List<&2, String>) -> Bool:
  match values:
    case Nil{}: True{}
    case +value <> tail:
      Bool.and(Bool.or(String.eq(value, "true"), String.eq(value, "false")),
        read_flags(tail))

# A count's values are non-empty decimal digits, which count reads with
# Nat.read: what the scan records for each occurrence, or what env or the
# default gives once valid_nat accepts it.
def read_counts(values: List<&2, String>) -> Bool:
  match values:
    case Nil{}: True{}
    case +value <> tail:
      Bool.and(Bool.and(Bool.not(String.is_empty(value)),
        Cli.decimal_digits(value)), read_counts(tail))

def read_one(values: List<&2, String>) -> Bool:
  match values:
    case Nil{}: False{}
    case value <> tail: List.is_empty(&2, String, tail)

def read_most_one(values: List<&2, String>) -> Bool:
  match values:
    case Nil{}: True{}
    case value <> tail: List.is_empty(&2, String, tail)

def read_form(form: Cli.Form, values: List<&2, String>) -> Bool:
  match form:
    case Cli.ReadOne{}: read_one(values)
    case Cli.ReadOpt{}: read_most_one(values)
    case Cli.ReadMany{}: True{}

def read_choose(opt: Bool, values: List<&2, String>) -> Bool:
  match opt:
    case True{}: read_most_one(values)
    case False{}: read_one(values)

def read_keys(values: List<&2, String>, +keys: List<&2, String>) -> Bool:
  match values:
    case Nil{}: True{}
    case value <> tail:
      Bool.and(List.contains(~String, ~String.eq, keys, value),
        read_keys(tail, keys))

# What want's reader may read: values its type accepts, one for a bare
# reader or choose, at most one for _opt, choose_opt, flag and count, a
# flag's as "true" or "false", a count's as digits, and choose's among its
# keys; program and program_opt read any strings.
def read_good(want: Cli.Want, +values: List<&2, String>) -> Bool:
  match want:
    case Cli.WFlag{}: Bool.and(read_flags(values), read_most_one(values))
    case Cli.WCount{}: Bool.and(read_counts(values), read_most_one(values))
    case Cli.WValue{stem, form}:
      Bool.and(read_all(values, stem), read_form(form, values))
    case Cli.WAny{}: True{}
    case Cli.WChoose{opt, keys}:
      Bool.and(read_choose(opt, values), read_keys(values, keys))
    case Cli.WProgram{opt}: True{}

# Once the verdict passes, the reader reads only what read_good allows.
def read_at(verdict: Maybe<&2, String>, want: Cli.Want,
    values: List<&2, String>) -> Bool:
  match verdict:
    case None{}: read_good(want, values)
    case Some{msg}: True{}

def read_parsed(found: Maybe<&2, Cli.Matches>, +id: String,
    +want: Cli.Want) -> Type:
  match found:
    case None{}: Unit
    case Some{Cli.Matches{cmd, +path, fields, external}}:
      {read_at(Cli.verdict(cmd, path, id, want), want,
        Cli.field_values(Cli.field_find(fields, id))) == True{} : Bool}

# P21: on any argv that a lint-clean command parses, a reader, choose or
# choose_opt whose verdict passes reads only what the parse validated, so it
# never fails (SPEC 6.5): the field its id finds holds values its type
# accepts, one for a bare reader or choose, and choose's among its keys.
law p21:
  for +c: Cli.Cmd
  for h: Cli.Host
  for argv: List<&2, String>
  for +id: String
  for +want: Cli.Want
  {Cli.problems(c) == [] : List<&2, Cli.Problem>} ->
  read_parsed(Cli.matches(c, Cli.parse(c, h, argv)), id, want)

# P21: so does the sample at any path of a lint-clean command.
law p21_sample:
  for +c: Cli.Cmd
  for +path: List<&2, String>
  for +id: String
  for +want: Cli.Want
  {Cli.problems(c) == [] : List<&2, Cli.Problem>} ->
  {read_at(Cli.verdict(c, path, id, want), want,
    Cli.field_values(Cli.field_find(Cli.sample_fields(c, path), id)))
    == True{} : Bool}

# Each of ms read as a decoder reads it, through its own command and path.
def samples_read(ms: List<&2, Cli.Matches>, +id: String, +want: Cli.Want) ->
    Bool:
  match ms:
    case Nil{}: True{}
    case Cli.Matches{cmd, +path, fields, external} <> tail:
      Bool.and(read_at(Cli.verdict(cmd, path, id, want), want,
        Cli.field_values(Cli.field_find(fields, id))),
        samples_read(tail, id, want))

# P21: and so does every sample check runs the decoder on at any path of a
# lint-clean command, each other state of an arg included: a state check
# tries is one the readers whose verdict passes can read.
law p21_samples:
  for +c: Cli.Cmd
  for +path: List<&2, String>
  for +id: String
  for +want: Cli.Want
  {Cli.problems(c) == [] : List<&2, Cli.Problem>} ->
  {samples_read(Cli.samples(c, path), id, want) == True{} : Bool}

# P22: valid_nat, which parse, lint and check apply to a Nat value, accepts
# exactly the strings Nat.read reads, so nat_of never falls back to 0 on a
# value that passed it.
law p22_nat:
  for +v: String
  {Cli.valid_nat(v) == Maybe.is_some(&2, Nat, Nat.read(v)) : Bool}

# P22: so does valid_u32 for U32.read, which u32_of reads with.
law p22_u32:
  for +v: String
  {Cli.valid_u32(v) == Maybe.is_some(&2, U32, U32.read(v)) : Bool}

# Whether keys are found's values as a set: not empty, none missing, and none
# extra.
def keys_are(+keys: List<&2, String>,
    found: Maybe<&2, List<&2, String>>) -> Bool:
  match found:
    case None{}: False{}
    case Some{+values}:
      Bool.and(Bool.not(List.is_empty(&2, String, keys)),
        Bool.and(read_keys(keys, values), read_keys(values, keys)))

# P22: choose and choose_opt's verdict on an arg passes only with a table
# whose keys are the arg's one_of values as a set (g_check_choose); p19_verdict
# names the arg.
law p22_choose:
  for opt: Bool
  for +keys: List<&2, String>
  for +id: String
  for +kind: Cli.UsageKind
  for +attrs: List<&2, Cli.Item>
  {Cli.want_verdict(Cli.WChoose{opt, keys}, id, kind, attrs)
    == None{} : Maybe<&2, String>} ->
  {keys_are(keys, Cli.find_one_of(attrs)) == True{} : Bool}

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

# sampled()'s sample at s, field by field.
def s_base() -> List<&2, Cli.Field>:
  [
    Cli.Field{"verbose", ["1"], Cli.Argv{}},
    Cli.Field{"flag", ["true"], Cli.Argv{}},
    Cli.Field{"pos", ["true"], Cli.Argv{}},
    Cli.Field{"neg", ["false"], Cli.Default{}},
    Cli.Field{"name", ["anon"], Cli.Default{}},
    Cli.Field{"mode", ["fast"], Cli.Argv{}},
    Cli.Field{"num", ["0"], Cli.Argv{}},
    Cli.Field{"uint", ["0"], Cli.Argv{}},
    Cli.Field{"real", ["0.0"], Cli.Argv{}},
    Cli.Field{"yes", ["false"], Cli.Argv{}},
    Cli.Field{"tag", ["a", "b"], Cli.Default{}},
    Cli.Field{"file", ["x"], Cli.Argv{}},
  ]

# fields with each field named id replaced by f.
def swap(fields: List<&2, Cli.Field>, +id: String, +f: Cli.Field) ->
    List<&2, Cli.Field>:
  match fields:
    case Nil{}: Nil{}
    case Cli.Field{+key, values, source} <> tail:
      Bool.pick(Cli.Field, String.eq(key, id), f,
        Cli.Field{key, values, source}) <> swap(tail, id, f)

# sampled()'s sample at s with id's field holding values from src.
def s_with(+id: String, values: List<&2, String>, src: Cli.Src) ->
    Cli.Matches:
  Cli.Matches{sampled(), ["s"], swap(s_base(), id, Cli.Field{id, values, src}),
    None{}}

def key_tool() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--key <K>", "Key", [Cli.required(), Cli.one_of(["a", "b", "c"])]),
    Cli.arg("[ARG]...", "Args", []),
  ])

# G-CHECK: samples lists what check runs the decoder on at a path: the
# sample, then for each arg in scope in turn each other state parse can give
# it, with every other arg as in the sample. An arg's states are left out
# (Absent, no values), unless it is required, a required positional or has
# a default, then given each of its listed values: its one_of values, else
# true and false for a negatable flag, false and true for an as_bool value,
# else the sample's value by type. A state the sample already has is
# skipped, and an arg with a default is given each listed value.
law g_check_states:
  {Cli.sample(sampled(), ["s"]) ==
    Cli.Matches{sampled(), ["s"], s_base(), None{}} : Cli.Matches} &
  {Cli.samples(sampled(), ["s"]) == [
    Cli.Matches{sampled(), ["s"], s_base(), None{}},
    s_with("verbose", [], Cli.Absent{}),
    s_with("flag", [], Cli.Absent{}),
    s_with("pos", [], Cli.Absent{}),
    s_with("pos", ["false"], Cli.Argv{}),
    s_with("neg", ["true"], Cli.Argv{}),
    s_with("neg", ["false"], Cli.Argv{}),
    s_with("name", ["x"], Cli.Argv{}),
    s_with("mode", [], Cli.Absent{}),
    s_with("mode", ["slow"], Cli.Argv{}),
    s_with("num", [], Cli.Absent{}),
    s_with("uint", [], Cli.Absent{}),
    s_with("real", [], Cli.Absent{}),
    s_with("yes", [], Cli.Absent{}),
    s_with("yes", ["true"], Cli.Argv{}),
    s_with("tag", ["x"], Cli.Argv{}),
  ] : List<&2, Cli.Matches>} &
  {Cli.samples(sampled(), []) == [
    Cli.Matches{sampled(), [], [Cli.Field{"verbose", ["1"], Cli.Argv{}},
      Cli.Field{"root", ["x"], Cli.Argv{}}], None{}},
    Cli.Matches{sampled(), [], [Cli.Field{"verbose", [], Cli.Absent{}},
      Cli.Field{"root", ["x"], Cli.Argv{}}], None{}},
    Cli.Matches{sampled(), [], [Cli.Field{"verbose", ["1"], Cli.Argv{}},
      Cli.Field{"root", [], Cli.Absent{}}], None{}},
  ] : List<&2, Cli.Matches>} &
  {Cli.samples(key_tool(), []) == [
    Cli.Matches{key_tool(), [], [Cli.Field{"key", ["a"], Cli.Argv{}},
      Cli.Field{"arg", ["x"], Cli.Argv{}}], None{}},
    Cli.Matches{key_tool(), [], [Cli.Field{"key", ["b"], Cli.Argv{}},
      Cli.Field{"arg", ["x"], Cli.Argv{}}], None{}},
    Cli.Matches{key_tool(), [], [Cli.Field{"key", ["c"], Cli.Argv{}},
      Cli.Field{"arg", ["x"], Cli.Argv{}}], None{}},
    Cli.Matches{key_tool(), [], [Cli.Field{"key", ["a"], Cli.Argv{}},
      Cli.Field{"arg", [], Cli.Absent{}}], None{}},
  ] : List<&2, Cli.Matches>}

# A Bug with msg when hit, else Done.
def bug_if(hit: Bool, msg: String) -> Cli.Dec(Bool):
  match hit:
    case True{}: Cli.bug(Bool, msg)
    case False{}: Done{False{}}

# Reads "nope", which no command of sampled() has, when hit.
def nope_if(hit: Bool, m: Cli.Matches) -> Cli.Dec(Bool):
  match hit:
    case True{}: Cli.flag(m, "nope")
    case False{}: Done{False{}}

def off_nope(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    on : Bool <- Cli.flag(m, "flag")
    nope_if(Bool.not(on), m)

def quiet(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    verbose : Nat <- Cli.count(m, "verbose")
    bug_if(Nat.is_eq(verbose, 0n), "quiet")

def no_pos(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    pos : Bool <- Cli.flag(m, "pos")
    given : Bool <- Cli.given(m, "pos")
    bug_if(Bool.and(Bool.not(pos), given), "no-pos")

def neg_on(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    neg : Bool <- Cli.flag(m, "neg")
    bug_if(neg, "neg")

def named(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    given : Bool <- Cli.given(m, "name")
    bug_if(given, "named")

def renamed(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    +name : String <- Cli.str(m, "name")
    bug_if(Bool.not(String.eq(name, "anon")), name)

def bob(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    name : String <- Cli.str(m, "name")
    bug_if(String.eq(name, "bob"), "bob")

def yes_true(found: Maybe<&2, Bool>) -> Bool:
  match found:
    case Some{yes}: yes
    case None{}: False{}

def yes_on(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    yes : Maybe<&2, Bool> <- Cli.bool_opt(m, "yes")
    bug_if(yes_true(yes), "yes")

def tagged(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    tags : List<&2, String> <- Cli.strs(m, "tag")
    bug_if(String.eq(String.join(tags, ","), "x"), "tag x")

def mode_text(found: Maybe<&2, String>) -> String:
  match found:
    case Some{mode}: mode
    case None{}: "none"

def mode_bug(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    mode : Maybe<&2, String> <- Cli.str_opt(m, "mode")
    Cli.bug(Bool, mode_text(mode))

def mode_slow(found: Maybe<&2, String>) -> Bool:
  match found:
    case Some{mode}: String.eq(mode, "slow")
    case None{}: False{}

def both(+m: Cli.Matches) -> Cli.Dec(Bool):
  do Cli.Dec<Bool>:
    on : Bool <- Cli.flag(m, "flag")
    mode : Maybe<&2, String> <- Cli.str_opt(m, "mode")
    bug_if(Bool.and(Bool.not(on), mode_slow(mode)), "both")

# G-CHECK: check runs the decoder on every sample samples lists, so a read
# or Bug that only another state of one arg reaches is reported: a flag
# left out, a global count left out, a negatable flag given false, a
# defaulted one given true, a defaulted value given, or given another
# value, an as_bool value given true, a list given one value, and an
# optional value left out or given a later one_of value. Each Bug is listed
# once per path, in the order its first sample comes; a Bug that needs two
# args out of the sample's state, or a value no state gives, is not found.
law g_check_branches:
  {Cli.check(~Bool, ~off_nope, sampled()) == [
    Cli.DecodeBug{"tool s", "'nope' is not an argument of 'tool s'"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~quiet, sampled()) ==
    [Cli.DecodeBug{"tool s", "quiet"}] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~no_pos, sampled()) ==
    [Cli.DecodeBug{"tool s", "no-pos"}] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~neg_on, sampled()) ==
    [Cli.DecodeBug{"tool s", "neg"}] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~named, sampled()) ==
    [Cli.DecodeBug{"tool s", "named"}] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~renamed, sampled()) ==
    [Cli.DecodeBug{"tool s", "x"}] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~yes_on, sampled()) ==
    [Cli.DecodeBug{"tool s", "yes"}] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~tagged, sampled()) ==
    [Cli.DecodeBug{"tool s", "tag x"}] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~mode_bug, sampled()) == [
    Cli.DecodeBug{"tool s", "fast"},
    Cli.DecodeBug{"tool s", "none"},
    Cli.DecodeBug{"tool s", "slow"},
  ] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~(+m => Cli.bug(Bool, "b")), sampled()) ==
    [Cli.DecodeBug{"tool s", "b"}] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~both, sampled()) == [] : List<&2, Cli.Problem>} &
  {Cli.check(~Bool, ~bob, sampled()) == [] : List<&2, Cli.Problem>}

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

type Tries is Data:
  Tries{times: Nat, program: Cli.Program}

def tries(+m: Cli.Matches) -> Cli.Dec(Tries):
  do Cli.Dec<Tries>:
    times : Nat <- Cli.nat(m, "times")
    program : Cli.Program <- Cli.program(m, "command")
    return Tries{times, program}

def tries_opt(+m: Cli.Matches) -> Cli.Dec(Maybe<&2, Cli.Program>):
  Cli.program_opt(m, "command")

# G-READ: program reads a rest() slot's first value as the program and every
# later value, options and "--" included, as its arguments, in order;
# program_opt reads an empty slot as None.
law g_read_program:
  {decoded(~Tries, ~tries, wrapper("<COMMAND>...", [Cli.rest()]), host(),
    ["curl", "--help"]) ==
    Some{Done{Tries{3n, Cli.Program{"curl", ["--help"]}}}}
    : Maybe<Cli.Dec(Tries)>} &
  {decoded(~Tries, ~tries, wrapper("<COMMAND>...", [Cli.rest()]), host(),
    ["-n", "5", "curl", "-n", "1", "--", "x"]) ==
    Some{Done{Tries{5n, Cli.Program{"curl", ["-n", "1", "--", "x"]}}}}
    : Maybe<Cli.Dec(Tries)>} &
  {decoded(~Tries, ~tries, wrapper("<COMMAND>...", [Cli.rest()]), host(),
    ["--", "-n"]) == Some{Done{Tries{3n, Cli.Program{"-n", []}}}}
    : Maybe<Cli.Dec(Tries)>} &
  {decoded(~Tries, ~tries, wrapper("<COMMAND>...", [Cli.rest()]), host(),
    ["curl"]) == Some{Done{Tries{3n, Cli.Program{"curl", []}}}}
    : Maybe<Cli.Dec(Tries)>} &
  {decoded(~Tries, ~tries,
    wrapper("[COMMAND]...", [Cli.rest(), Cli.default("true")]), host(),
    []) == Some{Done{Tries{3n, Cli.Program{"true", []}}}}
    : Maybe<Cli.Dec(Tries)>} &
  {decoded(~Maybe<&2, Cli.Program>, ~tries_opt,
    wrapper("[COMMAND]...", [Cli.rest()]), host(), []) ==
    Some{Done{None{}}} : Maybe<Cli.Dec(Maybe<&2, Cli.Program>)>} &
  {decoded(~Maybe<&2, Cli.Program>, ~tries_opt,
    wrapper("[COMMAND]...", [Cli.rest()]), host(),
    ["--tag", "a", "sh", "-c", "exit 1"]) ==
    Some{Done{Some{Cli.Program{"sh", ["-c", "exit 1"]}}}}
    : Maybe<Cli.Dec(Maybe<&2, Cli.Program>)>}

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

# G-HELP: the env tag lists every name in order.
law g_help_env_names:
  {Cli.help(env_chain(), [], False{}, host()) == page([
    "Tool",
    "",
    "Usage: tool [OPTIONS]",
    "",
    "Options:",
    "      --out <X>  Output [env: TOOL_OUT, LEGACY_OUT] [default: d]",
    "      --n <N>    Count [env: TOOL_N, LEGACY_N]",
    "  -h, --help     Print help",
  ]) : String}

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

# G-HELP: a subcommand's usage shows each need_one group it inherits, before
# its own, as E06 writes them, and a group it also needs one of once, among
# those it inherits; the rules list no options of their own.
law g_help_global_groups:
  {Cli.usage(fmt_tool(), ["run"])
    == "tool run [OPTIONS] --out <X> <--json|--yaml> [COMMAND]" : String} &
  {Cli.usage(fmt_tool(), ["run", "deep"])
    == "tool run deep [OPTIONS] --out <X> <--json|--yaml>" : String} &
  {Cli.usage(fmt_tool(), ["conv"])
    == "tool conv [OPTIONS] --out <X> <--json|--yaml|--toml>" : String} &
  {Cli.usage(group_scopes(), ["run"])
    == "tool run [OPTIONS] <--q|--r> <--c|--d>" : String} &
  {Cli.usage(group_scopes(), ["other"])
    == "tool other [OPTIONS] <--q>" : String} &
  {Cli.help(fmt_tool(), ["run"], False{}, host()) == page([
    "Run it",
    "",
    "Usage: tool run [OPTIONS] --out <X> <--json|--yaml> [COMMAND]",
    "",
    "Commands:",
    "  deep           Go deeper",
    "  help           Print this message or the help of the given subcommand(s)",
    "",
    "Options:",
    "      --json     JSON output",
    "      --yaml     YAML output",
    "      --out <X>  Output",
    "  -h, --help     Print help",
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

# An uncolored error page: message, tips, then the scope's usage.
def error_text(message: String, tips: List<&2, String>,
    usage: String) -> String:
  String.concat(["error: ", message, "\n", tip_block(tips), "\nUsage: ",
    usage, "\n\nFor more information, try '--help'.\n"])

# The uncolored outcome for an error.
def report(message: String, tips: List<&2, String>,
    usage: String) -> Cli.Outcome:
  Cli.Shown{2, "", error_text(message, tips, usage)}

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

# git with commit, alias ci, and remote, whose add takes no args; items go
# first in both commands.
def plugged(+items: List<&2, Cli.Item>) -> Cli.Cmd:
  Cli.cmd("git", "Git", List.append(&2, Cli.Item, items, [
    Cli.sub("commit", "Record changes", [Cli.alias("ci")]),
    Cli.sub("remote", "Manage remotes", List.append(&2, Cli.Item, items, [
      Cli.sub("add", "Add a remote", []),
    ])),
  ]))

# G-TIP: unknown_text is the E02 page eval prints for a name at path, with
# T4's similar subcommands and the scope's usage, in stderr's colors and the
# terminal's width, so an app with external() can report a name that no
# plugin answers to.
law g_tip_unknown:
  {Cli.unknown_text(plugged([Cli.external()]), [], "comit",
    Cli.Term{False{}, False{}, 80n}) ==
    error_text("unrecognized subcommand 'comit'",
      ["a similar subcommand exists: 'commit'"], "git [COMMAND]") : String} &
  {Cli.unknown_text(plugged([Cli.external()]), ["remote"], "ad",
    Cli.Term{False{}, False{}, 80n}) ==
    error_text("unrecognized subcommand 'ad'",
      ["a similar subcommand exists: 'add'"], "git remote [COMMAND]")
    : String} &
  {Cli.unknown_text(plugged([Cli.external()]), [], "zzz",
    Cli.Term{False{}, False{}, 80n}) ==
    error_text("unrecognized subcommand 'zzz'", [], "git [COMMAND]")
    : String} &
  {Cli.outcome(plugged([Cli.sub_optional()]), host(), ["remote", "ad"]) ==
    Cli.Shown{2, "", Cli.unknown_text(plugged([Cli.external()]),
      ["remote"], "ad", Cli.Term{True{}, False{}, 80n})} : Cli.Outcome} &
  {Cli.unknown_text(plugged([Cli.external()]), [], "comit",
    Cli.Term{False{}, True{}, 80n}) == String.concat([
      "\u{1B}[1;31merror:\u{1B}[0m unrecognized subcommand '",
      "\u{1B}[33mcomit\u{1B}[0m'\n\n  \u{1B}[1;32mtip:\u{1B}[0m ",
      "a similar subcommand exists: '\u{1B}[32mcommit\u{1B}[0m'\n\n",
      "\u{1B}[1;4mUsage:\u{1B}[0m \u{1B}[1mgit\u{1B}[0m [COMMAND]\n\n",
      "For more information, try '\u{1B}[1m--help\u{1B}[0m'.\n",
    ]) : String} &
  {Cli.unknown_text(plugged([Cli.external(),
    Cli.arg("--work-tree <PATH>", "Work tree", [Cli.required()])]),
    ["remote"], "ad", Cli.Term{False{}, False{}, 40n}) ==
    error_text("unrecognized subcommand 'ad'",
      ["a similar subcommand exists: 'add'"],
      "git remote --work-tree <PATH>\n       [COMMAND]") : String}

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

# G-LINT BadStatus: usage_status takes an exit status from 1 to 255, and
# lint checks each one at the root, in item order. On a subcommand or an arg
# it is Misplaced, whatever its code. Two at the root pass lint; the first
# sets usage_code (G-ERR).
law g_lint_status:
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.usage_status(1),
    Cli.usage_status(255),
  ])) == [] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool", [Cli.usage_status(0)]))
    == [Cli.BadStatus{"tool", 0}] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool", [Cli.usage_status(256)]))
    == [Cli.BadStatus{"tool", 256}] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.arg("-v", "Verbose", []),
    Cli.usage_status(0),
    Cli.arg("-v", "Verbose again", []),
  ])) == [Cli.BadStatus{"tool", 0}, Cli.Dup{"tool", "-v"}]
    : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.sub("run", "Run", [Cli.usage_status(0)]),
  ])) == [Cli.Misplaced{"tool run", "usage_status"}] : List<&2, Cli.Problem>} &
  {Cli.problems(Cli.cmd("tool", "Tool", [
    Cli.arg("--ok", "Accept", [Cli.usage_status(125)]),
  ])) == [Cli.Misplaced{"tool", "usage_status"}] : List<&2, Cli.Problem>} &
  {Cli.problem_line(Cli.BadStatus{"tool", 256})
    == "  tool: usage_status(256) is not an exit status from 1 to 255"
    : String}

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

# M5: eval answers outcome's Shown as Quit and decodes a Matched (V7).
# eval_with is eval with the decoder passed as a value, so a law can
# quantify over decoders. eval must be a direct forwarding definition,
# eval(~A, ~decode, c, h, argv) = eval_with(A, decode, c, h, argv), so P10
# and P11, proved of eval_with, carry to every eval; eval_bridge checks it.

# P24: usage_code is an exit status from 1 to 255: 2, or the code of a
# usage_status among the root's items. P10 and P11 range over it, so a spec
# whose root sets none ends a usage error with 2.
def status_named(items: List<&2, Cli.Item>, +code: U32) -> Bool:
  match items:
    case Nil{}: False{}
    case Cli.UsageStatus{n} <> tail:
      Bool.or(U32.is_eq(n, code), status_named(tail, code))
    case head <> tail: status_named(tail, code)

def p24_code(+code: U32, items: List<&2, Cli.Item>) -> Bool:
  Bool.and(Bool.and(U32.is_le(1, code), U32.is_le(code, 255)),
    Bool.or(U32.is_eq(code, 2), status_named(items, code)))

law p24:
  for name: String
  for about: String
  for +items: List<&2, Cli.Item>
  {p24_code(Cli.usage_code(Cli.cmd(name, about, items)), items) == True{}
    : Bool}

# P10: for every decoder, eval_with answers Go, or Quit with code 0, 70 or
# the spec's usage_code.
def p10_code(-A: Type, s: Cli.Step<A>, usage: U32) -> Bool:
  match s:
    case Cli.Go{value, term}: True{}
    case Cli.Quit{+code, out, err}:
      Bool.or(U32.is_eq(code, 0),
        Bool.or(U32.is_eq(code, usage), U32.is_eq(code, 70)))

law p10:
  for -A: Type
  for decode: @+m: Cli.Matches -> Cli.Dec(A)
  for +c: Cli.Cmd
  for h: Cli.Host
  for argv: List<&2, String>
  {p10_code(A, Cli.eval_with(A, decode, c, h, argv), Cli.usage_code(c))
    == True{} : Bool}

# P11: for every decoder, eval_with's exit 0 leaves stderr empty, and its
# exits 70 and the spec's usage_code leave stdout empty.
def p11_streams(-A: Type, s: Cli.Step<A>, usage: U32) -> Bool:
  match s:
    case Cli.Go{value, term}: True{}
    case Cli.Quit{+code, out, err}:
      Bool.and(Bool.or(Bool.not(U32.is_eq(code, 0)), String.is_empty(err)),
        Bool.or(Bool.not(Bool.or(U32.is_eq(code, usage),
          U32.is_eq(code, 70))), String.is_empty(out)))

law p11:
  for -A: Type
  for decode: @+m: Cli.Matches -> Cli.Dec(A)
  for +c: Cli.Cmd
  for h: Cli.Host
  for argv: List<&2, String>
  {p11_streams(A, Cli.eval_with(A, decode, c, h, argv), Cli.usage_code(c))
    == True{} : Bool}

# eval is eval_with with its template arguments as values: with keep for
# every spec, and with pkg's decoder.
law eval_bridge:
  for +c: Cli.Cmd
  for +h: Cli.Host
  for +argv: List<&2, String>
  {Cli.eval(~Cli.Matches, ~Cli.keep, c, h, argv)
    == Cli.eval_with(Cli.Matches, Cli.keep, c, h, argv)
    : Cli.Step<Cli.Matches>} &
  {Cli.eval(~Demo.Action, ~Demo.decode, Demo.cli(), h, argv)
    == Cli.eval_with(Demo.Action, Demo.decode, Demo.cli(), h, argv)
    : Cli.Step<Demo.Action>}

# Lint once: linted lints a spec, returning either a Linted or its problems;
# eval_linted evals the Linted without linting it again. outcome_linted is
# outcome without the lint; eval_linted_with passes the decoder as a value,
# and eval_linted forwards to it as eval does to eval_with.

# P16: on the Linted that linted returns, outcome_linted answers as outcome
# does on its spec. through_linted renders the saved problems on failure.
# eval_with_step and eval_linted_step carry P16 to eval_with and
# eval_linted_with for every decoder: a law can use a decoder only once.
def through_linted(found: Result<&2, &2, List<&2, Cli.Problem>, Cli.Linted>,
    c: Cli.Cmd, h: Cli.Host, argv: List<&2, String>) -> Cli.Outcome:
  match found:
    case Fail{ps}: Cli.outcome_lint(ps, c, h, argv)
    case Done{l}: Cli.outcome_linted(l, h, argv)

law p16:
  for +c: Cli.Cmd
  for +h: Cli.Host
  for +argv: List<&2, String>
  {through_linted(Cli.linted(c), c, h, argv) == Cli.outcome(c, h, argv)
    : Cli.Outcome}

law eval_with_step:
  for -A: Type
  for decode: @+m: Cli.Matches -> Cli.Dec(A)
  for c: Cli.Cmd
  for +h: Cli.Host
  for +argv: List<&2, String>
  {Cli.eval_with(A, decode, c, h, argv)
    == Cli.eval_step(A, decode, Cli.outcome(c, h, argv), h, argv)
    : Cli.Step<A>}

law eval_linted_step:
  for -A: Type
  for decode: @+m: Cli.Matches -> Cli.Dec(A)
  for l: Cli.Linted
  for +h: Cli.Host
  for +argv: List<&2, String>
  {Cli.eval_linted_with(A, decode, l, h, argv)
    == Cli.eval_step(A, decode, Cli.outcome_linted(l, h, argv), h, argv)
    : Cli.Step<A>}

# P17: linted returns a Linted exactly when lint finds no problem, and its
# failure carries the same problems, in order.
def linted_problems(
    found: Result<&2, &2, List<&2, Cli.Problem>, Cli.Linted>) ->
    List<&2, Cli.Problem>:
  match found:
    case Fail{ps}: ps
    case Done{l}: []

law p17:
  for +c: Cli.Cmd
  {Result.is_done(&2, &2, List<&2, Cli.Problem>, Cli.Linted, Cli.linted(c))
    == List.is_empty(&2, Cli.Problem, Cli.problems(c)) : Bool} &
  {linted_problems(Cli.linted(c)) == Cli.problems(c)
    : List<&2, Cli.Problem>}

# P10 and P11 hold of eval_linted_with for every Linted, including one
# built from a spec that lint rejects, against its spec's usage_code.
def linted_usage(l: Cli.Linted) -> U32:
  match l:
    case Cli.Linted{c}: Cli.usage_code(c)

law p10_linted:
  for -A: Type
  for decode: @+m: Cli.Matches -> Cli.Dec(A)
  for +l: Cli.Linted
  for h: Cli.Host
  for argv: List<&2, String>
  {p10_code(A, Cli.eval_linted_with(A, decode, l, h, argv), linted_usage(l))
    == True{} : Bool}

law p11_linted:
  for -A: Type
  for decode: @+m: Cli.Matches -> Cli.Dec(A)
  for +l: Cli.Linted
  for h: Cli.Host
  for argv: List<&2, String>
  {p11_streams(A, Cli.eval_linted_with(A, decode, l, h, argv),
    linted_usage(l)) == True{} : Bool}

# eval_linted is eval_linted_with with its template arguments as values:
# with keep, and with pkg's decoder, for every Linted.
law eval_linted_bridge:
  for +l: Cli.Linted
  for +h: Cli.Host
  for +argv: List<&2, String>
  {Cli.eval_linted(~Cli.Matches, ~Cli.keep, l, h, argv)
    == Cli.eval_linted_with(Cli.Matches, Cli.keep, l, h, argv)
    : Cli.Step<Cli.Matches>} &
  {Cli.eval_linted(~Demo.Action, ~Demo.decode, l, h, argv)
    == Cli.eval_linted_with(Demo.Action, Demo.decode, l, h, argv)
    : Cli.Step<Demo.Action>}

# The parse a decoder sees, without the spec it came from.
type Parsed is Data:
  Parsed{path: List<&2, String>, fields: List<&2, Cli.Field>,
    external: Maybe<&2, Cli.ExternalArgs>}

def parsed(+m: Cli.Matches) -> Cli.Dec(Parsed):
  match m:
    case Cli.Matches{cmd, path, fields, external}:
      Done{Parsed{path, fields, external}}

def ran(c: Cli.Cmd, h: Cli.Host,
    argv: List<&2, String>) -> Cli.Step<Parsed>:
  Cli.eval(~Parsed, ~parsed, c, h, argv)

# Go at the root without an external call; host() gives no color, width 80.
def went(fields: List<&2, Cli.Field>) -> Cli.Step<Parsed>:
  Cli.Go{Parsed{[], fields, None{}}, Cli.Term{False{}, False{}, 80n}}

def went_to(path: List<&2, String>, fields: List<&2, Cli.Field>,
    external: Maybe<&2, Cli.ExternalArgs>) -> Cli.Step<Parsed>:
  Cli.Go{Parsed{path, fields, external}, Cli.Term{False{}, False{}, 80n}}

def failed(-A: Type, message: String, tips: List<&2, String>,
    usage: String) -> Cli.Step<A>:
  Cli.Quit{2, "", error_text(message, tips, usage)}

# G-LEX through G-REL through eval: each M2 case's Go value, or its exact
# help, version or error bytes with their tips (§12.2). Each law covers
# every distinct input of the M2 law named without the `_eval` suffix.

law g_lex_cluster_eval:
  {ran(flags(), host(), ["-abc"]) ==
    went([
      field("a", ["true"], Cli.Argv{}),
      field("b", ["true"], Cli.Argv{}),
      field("c", ["true"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>}

law g_lex_values_eval:
  {ran(out_option(), host(), ["-ofile"]) ==
    went([
      field("out", ["file"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(out_option(), host(), ["-o=file"]) ==
    went([
      field("out", ["file"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(out_option(), host(), ["-o", "file"]) ==
    went([
      field("out", ["file"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(out_option(), host(), ["--out=file"]) ==
    went([
      field("out", ["file"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(out_option(), host(), ["--out", "file"]) ==
    went([
      field("out", ["file"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(out_option(), host(), ["--out="]) ==
    went([
      field("out", [""], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(out_option(), host(), ["-o"]) ==
    failed(Parsed,
      "a value is required for '--out <FILE>' but none was supplied",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_lex_end_eval:
  {ran(optional_operand(), host(), ["-"]) ==
    went([
      field("x", ["-"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(optional_operand(), host(), ["--", "-x"]) ==
    went([
      field("x", ["-x"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>}

law g_lex_count_eval:
  {ran(count_option(), host(), ["-vvv"]) ==
    went([
      field("verbose", ["3"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>}

law g_lex_negation_eval:
  {ran(negatable_option(), host(), ["--no-x"]) ==
    went([
      field("x", ["false"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(negatable_option(), host(), ["--x", "--no-x"]) ==
    went([
      field("x", ["false"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>}

law g_lex_bare_eval:
  {ran(color_option(), host(), ["--color"]) ==
    went([
      field("color", ["auto"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>}

law g_lex_errors_eval:
  {ran(decimal_option(False{}), host(), ["-m", "-5"]) ==
    failed(Parsed, "a value is required for '-m <NUM>' but none was supplied",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(decimal_option(True{}), host(), ["-m", "-5"]) ==
    went([
      field("m", ["-5"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--flag", "Flag", []),
  ]), host(), ["--flag=x"]) ==
    failed(Parsed,
      "unexpected value 'x' for '--flag' found; no more were expected",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("-a", "Flag a", []),
  ]), host(), ["-az"]) ==
    failed(Parsed, "unexpected argument '-z' found",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_lex_recovery_eval:
  {ran(flags(), host(), ["--bad=x", "--help"]) ==
    Cli.Quit{0, page([
      "Tool",
      "",
      "Usage: tool [OPTIONS]",
      "",
      "Options:",
      "  -a          Flag a",
      "  -b          Flag b",
      "  -c          Flag c",
      "  -h, --help  Print help",
    ]), ""} : Cli.Step<Parsed>}

law g_pos_variadic_eval:
  {ran(cp(), host(), ["a", "b", "dest"]) ==
    went([
      field("src", ["a", "b"], Cli.Argv{}),
      field("dst", ["dest"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(cp(), host(), ["a", "dest"]) ==
    went([
      field("src", ["a"], Cli.Argv{}),
      field("dst", ["dest"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(cp(), host(), ["dest"]) ==
    failed(Parsed,
      "the following required arguments were not provided:\n  <SRC>...",
      [], "cp <SRC>... <DST>") : Cli.Step<Parsed>}

law g_pos_cases_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("[OUT]", "Output", []),
  ]), host(), []) ==
    went([]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("<X>", "Operand", []),
  ]), host(), ["a", "b"]) ==
    failed(Parsed, "unexpected argument 'b' found",
      [], "tool <X>") : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("<ITEM>...", "Items", [Cli.rest()]),
  ]), host(), ["a", "--", "-x"]) ==
    went([
      field("item", ["a", "--", "-x"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("<X>", "Operand", [Cli.hyphen()]),
  ]), host(), ["-x"]) ==
    went([
      field("x", ["-x"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("[X]", "Operand", []),
  ]), host(), [""]) ==
    went([
      field("x", [""], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("<N>", "Number", [Cli.as_f32()]),
  ]), host(), ["-5"]) ==
    went([
      field("n", ["-5"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("<N>", "Number", [Cli.as_nat()]),
  ]), host(), ["x"]) ==
    failed(Parsed,
      "invalid value 'x' for '<N>': expected a whole number from 0 to 281474976710655",
      [], "tool <N>") : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("<X>", "Operand", [Cli.hyphen()]),
  ]), host(), ["-h"]) ==
    Cli.Quit{0, page([
      "Tool",
      "",
      "Usage: tool <X>",
      "",
      "Arguments:",
      "  <X>         Operand",
      "",
      "Options:",
      "  -h, --help  Print help",
    ]), ""} : Cli.Step<Parsed>}

law g_pos_variadic_dash_eval:
  {ran(dash_operands(), host(), ["a", "-x", "-v", "-y"]) ==
    went([
      field("v", ["true"], Cli.Argv{}),
      field("x", ["a", "-x", "-y"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(f32_operands(), host(), ["1", "-5", "-6.5"]) ==
    went([
      field("n", ["1", "-5", "-6.5"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(f32_operands(), host(), ["1", "-5", "-x"]) ==
    failed(Parsed, "unexpected argument '-x' found",
      ["to pass '-x' as a value, use '-- -x'"], "tool <N>...")
    : Cli.Step<Parsed>}

law g_pos_hyphen_long_eval:
  {ran(dash_operands(), host(), ["--x=1", "-v", "--y"]) ==
    went([
      field("v", ["true"], Cli.Argv{}),
      field("x", ["--x=1", "--y"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(dash_operands(), host(), ["a", "--help"]) ==
    Cli.Quit{0, page([
      "Tool",
      "",
      "Usage: tool [OPTIONS] <X>...",
      "",
      "Arguments:",
      "  <X>...      Operands",
      "",
      "Options:",
      "  -v          Verbose",
      "  -h, --help  Print help",
    ]), ""} : Cli.Step<Parsed>}

law g_pos_rest_dash_eval:
  {ran(retry(), host(), ["curl", "-fsS", "-v", "url"]) ==
    went([
      field("command", ["curl"], Cli.Argv{}),
      field("args", ["-fsS", "-v", "url"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(retry(), host(), ["curl", "--max-time=5", "--", "url"]) ==
    went([
      field("command", ["curl"], Cli.Argv{}),
      field("args", ["--max-time=5", "--", "url"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(retry(), host(), ["curl", "-v", "-x"]) ==
    went([
      field("verbose", ["true"], Cli.Argv{}),
      field("command", ["curl"], Cli.Argv{}),
      field("args", ["-x"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(retry(), host(), ["curl", "--verbose=1"]) ==
    failed(Parsed,
      "unexpected value '1' for '--verbose' found; no more were expected",
      [], "retry [OPTIONS] <COMMAND> [ARGS]...") : Cli.Step<Parsed>} &
  {ran(retry(), host(), ["curl", "--help"]) ==
    Cli.Quit{0, page([
      "Retry a command",
      "",
      "Usage: retry [OPTIONS] <COMMAND> [ARGS]...",
      "",
      "Arguments:",
      "  <COMMAND>      Command",
      "  [ARGS]...      Arguments",
      "",
      "Options:",
      "  -v, --verbose  Verbose",
      "  -h, --help     Print help",
    ]), ""} : Cli.Step<Parsed>} &
  {ran(retry(), host(), ["-x", "curl"]) ==
    failed(Parsed, "unexpected argument '-x' found",
      ["to pass '-x' as a value, use '-- -x'"],
      "retry [OPTIONS] <COMMAND> [ARGS]...") : Cli.Step<Parsed>}

law g_sub_descent_eval:
  {ran(sub_tool(), host(), ["-g", "alpha", "-g", "--child"]) ==
    went_to(["alpha"], [
      field("global", ["true"], Cli.Argv{}),
      field("child", ["true"], Cli.Argv{}),
    ], None{}) : Cli.Step<Parsed>} &
  {ran(sub_tool(), host(), ["-g", "alpha", "--child"]) ==
    went_to(["alpha"], [
      field("global", ["true"], Cli.Argv{}),
      field("child", ["true"], Cli.Argv{}),
    ], None{}) : Cli.Step<Parsed>} &
  {ran(sub_tool(), host(), ["alpha", "-g"]) ==
    went_to(["alpha"], [
      field("global", ["true"], Cli.Argv{}),
    ], None{}) : Cli.Step<Parsed>}

law g_sub_alias_eval:
  {ran(sub_tool(), host(), ["a", "beta"]) ==
    went_to(["alpha", "beta"], [], None{}) : Cli.Step<Parsed>}

law g_sub_help_eval:
  {ran(sub_tool(), host(), ["help"]) ==
    Cli.Quit{0, page([
      "Tool",
      "",
      "Usage: tool [OPTIONS] <COMMAND>",
      "",
      "Commands:",
      "  alpha         Alpha [aliases: a]",
      "  help          Print this message or the help of the given subcommand(s)",
      "",
      "Options:",
      "      --root    Root only",
      "  -g, --global  Global flag",
      "  -h, --help    Print help",
    ]), ""} : Cli.Step<Parsed>} &
  {ran(sub_tool(), host(), ["help", "a", "beta"]) ==
    Cli.Quit{0, page([
      "Beta",
      "",
      "Usage: tool alpha beta [OPTIONS]",
      "",
      "Options:",
      "  -g, --global  Global flag",
      "  -h, --help    Print help",
    ]), ""} : Cli.Step<Parsed>} &
  {ran(sub_tool(), host(), ["help", "bad"]) ==
    failed(Parsed, "unrecognized subcommand 'bad'",
      [], "tool [OPTIONS] <COMMAND>") : Cli.Step<Parsed>} &
  {ran(sub_tool(), host(), ["alpha", "--help"]) ==
    Cli.Quit{0, page([
      "Alpha",
      "",
      "Usage: tool alpha [OPTIONS] [COMMAND]",
      "",
      "Commands:",
      "  beta          Beta",
      "  help          Print this message or the help of the given subcommand(s)",
      "",
      "Options:",
      "      --child   Child flag",
      "  -g, --global  Global flag",
      "  -h, --help    Print help",
    ]), ""} : Cli.Step<Parsed>}

law g_sub_scope_errors_eval:
  {ran(sub_tool(), host(), ["alpha", "--root"]) ==
    failed(Parsed,
      "unexpected argument '--root' found",
      ["'--root' belongs to 'tool'; place it before 'alpha'"],
      "tool alpha [OPTIONS] [COMMAND]") : Cli.Step<Parsed>} &
  {ran(sub_tool(), host(), ["--child", "alpha"]) ==
    failed(Parsed,
      "unexpected argument '--child' found",
      ["'--child' belongs to subcommand 'tool alpha'"],
      "tool [OPTIONS] <COMMAND>") : Cli.Step<Parsed>} &
  {ran(sub_tool(), host(), ["--alpha"]) ==
    failed(Parsed,
      "unexpected argument '--alpha' found",
      ["subcommand 'alpha' exists; to use it, remove the '--'"],
      "tool [OPTIONS] <COMMAND>") : Cli.Step<Parsed>}

law g_sub_external_eval:
  {ran(external_tool(), host(), ["plug", "--x", "--help"]) ==
    went_to([], [], Some{Cli.ExternalArgs{"plug", ["--x", "--help"]}})
     : Cli.Step<Parsed>} &
  {ran(external_tool(), host(), ["known"]) ==
    went_to(["known"], [], None{}) : Cli.Step<Parsed>}

law g_sub_missing_eval:
  {ran(sub_tool(), host(), ["-g"]) ==
    failed(Parsed,
      "'tool' requires a subcommand but none was provided\n  [subcommands: alpha, help]",
      [], "tool [OPTIONS] <COMMAND>") : Cli.Step<Parsed>} &
  {ran(sub_tool(), host(), []) ==
    Cli.Quit{2, "", page([
      "Tool",
      "",
      "Usage: tool [OPTIONS] <COMMAND>",
      "",
      "Commands:",
      "  alpha         Alpha [aliases: a]",
      "  help          Print this message or the help of the given subcommand(s)",
      "",
      "Options:",
      "      --root    Root only",
      "  -g, --global  Global flag",
      "  -h, --help    Print help",
    ])} : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.sub_optional(),
    Cli.sub("alpha", "Alpha", []),
  ]), host(), []) ==
    went([]) : Cli.Step<Parsed>}

law g_sub_short_shadow_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("-h", "Human", []),
  ]), host(), ["-h"]) ==
    went([
      field("h", ["true"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("-h", "Human", []),
  ]), host(), ["--help"]) ==
    Cli.Quit{0, page([
      "Tool",
      "",
      "Usage: tool [OPTIONS]",
      "",
      "Options:",
      "  -h          Human",
      "      --help  Print help",
    ]), ""} : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.version("1.0"),
    Cli.arg("-V", "Verbose", []),
  ]), host(), ["-V"]) ==
    went([
      field("V", ["true"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.version("1.0"),
    Cli.arg("-V", "Verbose", []),
  ]), host(), ["--version"]) ==
    Cli.Quit{0, page([
      "tool 1.0",
    ]), ""} : Cli.Step<Parsed>}

law g_val_strings_eval:
  {ran(typed([]), host(), ["--value="]) ==
    went([
      field("value", [""], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_file()]), host(), ["--value="]) ==
    went([
      field("value", [""], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_dir()]), host(), ["--value="]) ==
    went([
      field("value", [""], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([]), host(), ["--value=a", "--value=b"]) ==
    went([
      field("value", ["b"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>}

law g_val_nat_eval:
  {ran(typed([Cli.as_nat()]), host(), ["--value=0"]) ==
    went([
      field("value", ["0"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_nat()]), host(), ["--value=281474976710655"]) ==
    went([
      field("value", ["281474976710655"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_nat()]), host(), ["--value=281474976710656"]) ==
    failed(Parsed,
      "invalid value '281474976710656' for '--value <V>': expected a whole number from 0 to 281474976710655",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_nat()]), host(), ["--value=-1"]) ==
    failed(Parsed,
      "invalid value '-1' for '--value <V>': expected a whole number from 0 to 281474976710655",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_val_u32_eval:
  {ran(typed([Cli.as_u32()]), host(), ["--value=0"]) ==
    went([
      field("value", ["0"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_u32()]), host(), ["--value=4294967295"]) ==
    went([
      field("value", ["4294967295"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_u32()]), host(), ["--value=4294967296"]) ==
    failed(Parsed,
      "invalid value '4294967296' for '--value <V>': expected a whole number from 0 to 4294967295",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_val_f32_eval:
  {ran(typed([Cli.as_f32()]), host(), ["--value=-5"]) ==
    went([
      field("value", ["-5"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_f32()]), host(), ["--value=.5"]) ==
    went([
      field("value", [".5"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_f32()]), host(), ["--value=1e+3"]) ==
    went([
      field("value", ["1e+3"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_f32()]), host(), ["--value=1e"]) ==
    failed(Parsed,
      "invalid value '1e' for '--value <V>': expected a decimal number",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_f32()]), host(), ["--value=+3"]) ==
    failed(Parsed,
      "invalid value '+3' for '--value <V>': expected a decimal number",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_val_bool_eval:
  {ran(typed([Cli.as_bool()]), host(), ["--value=YeS"]) ==
    went([
      field("value", ["YeS"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_bool()]), host(), ["--value=0"]) ==
    went([
      field("value", ["0"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.as_bool()]), host(), ["--value=maybe"]) ==
    failed(Parsed,
      "invalid value 'maybe' for '--value <V>': expected true or false",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_val_one_of_eval:
  {ran(typed([Cli.one_of(["red", "blue"])]), host(), ["--value=red"]) ==
    went([
      field("value", ["red"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(typed([Cli.one_of(["red", "blue"])]), host(), ["--value=Red"]) ==
    failed(Parsed,
      "invalid value 'Red' for '--value <V>': expected one of 'red', 'blue'",
      ["a similar value exists: 'red'"], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_val_delim_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--tag <TAG>...", "Tags", [Cli.delim(',')]),
  ]), host(), ["--tag=a,b", "--tag=c"]) ==
    went([
      field("tag", ["a", "b", "c"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("<TAG>...", "Tags", [Cli.delim(',')]),
  ]), host(), ["a,b", "c"]) ==
    went([
      field("tag", ["a", "b", "c"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>}

law g_val_delim_typed_eval:
  {ran(numbers([Cli.as_nat(), Cli.delim(',')]),
    host(), ["--n=1,2", "--n", "3"]) ==
    went([
      field("n", ["1", "2", "3"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(number_operands([Cli.as_u32(), Cli.delim(',')]), host(), ["1,2"]) ==
    went([
      field("n", ["1", "2"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(numbers([Cli.as_bool(), Cli.delim(','), Cli.env("N")]),
    Cli.host_var(host(), "N", "yes,0"), []) ==
    went([
      field("n", ["yes", "0"], Cli.Env{}),
    ]) : Cli.Step<Parsed>} &
  {ran(numbers([Cli.one_of(["a", "b"]), Cli.delim(','), Cli.default("b,a")]),
    host(), []) ==
    went([
      field("n", ["b", "a"], Cli.Default{}),
    ]) : Cli.Step<Parsed>} &
  {ran(numbers([Cli.as_nat(), Cli.delim(',')]), host(), ["--n=1,x"]) ==
    failed(Parsed,
      "invalid value 'x' for '--n <N>...': expected a whole number from 0 to 281474976710655",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(numbers([Cli.as_nat(), Cli.delim(','), Cli.env("N")]),
    Cli.host_var(host(), "N", "1,x"), []) ==
    failed(Parsed,
      "invalid value 'x' for '--n <N>...' from environment variable N: expected a whole number from 0 to 281474976710655",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(number_operands([Cli.as_u32(), Cli.delim(',')]), host(), ["1,x,y"]) ==
    failed(Parsed,
      "invalid value 'x' for '<N>...': expected a whole number from 0 to 4294967295",
      [], "tool <N>...") : Cli.Step<Parsed>}

law g_val_delim_operands_eval:
  {ran(delim_files([]), host(), ["x,y", "-v", "--", "-v,a", "b,c"]) ==
    went([
      field("verbose", ["true"], Cli.Argv{}),
      field("files", ["x", "y", "-v", "a", "b", "c"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(delim_files([Cli.rest()]), host(),
    ["a,b", "-v,x", "--", "c,d", "-v"]) ==
    went([
      field("files", ["a", "b", "-v", "x", "--", "c", "d", "-v"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(delim_files([]), host(), ["--", ",a,,"]) ==
    went([
      field("files", ["", "a", "", ""], Cli.Argv{}),
    ]) : Cli.Step<Parsed>}

law g_src_env_eval:
  {ran(sourced(),
    Cli.host_var(Cli.host_var(Cli.host_var(host(),
      "TOOL_FLAG", "ON"), "TOOL_VERBOSE", "3"), "TOOL_VALUE", "env"), []) ==
    went([
      field("flag", ["true"], Cli.Env{}),
      field("verbose", ["3"], Cli.Env{}),
      field("value", ["env"], Cli.Env{}),
    ]) : Cli.Step<Parsed>}

law g_src_empty_default_eval:
  {ran(sourced(), Cli.host_var(host(), "TOOL_VALUE", ""), []) ==
    went([
      field("value", ["fallback"], Cli.Default{}),
    ]) : Cli.Step<Parsed>}

law g_src_precedence_eval:
  {ran(sourced(),
    Cli.host_var(host(), "TOOL_VALUE", "env"), ["--value=argv"]) ==
    went([
      field("value", ["argv"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(sourced(), Cli.host_var(host(), "TOOL_FLAG", "false"), ["--flag"]) ==
    went([
      field("flag", ["true"], Cli.Argv{}),
      field("value", ["fallback"], Cli.Default{}),
    ]) : Cli.Step<Parsed>} &
  {ran(sourced(),
    Cli.host_var(host(), "TOOL_VERBOSE", "7"), ["--verbose", "--verbose"]) ==
    went([
      field("verbose", ["2"], Cli.Argv{}),
      field("value", ["fallback"], Cli.Default{}),
    ]) : Cli.Step<Parsed>}

law g_src_invalid_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--value <V>", "Value", [Cli.as_nat(), Cli.env("TOOL_VALUE")]),
  ]), Cli.host_var(host(), "TOOL_VALUE", "nope"), []) ==
    failed(Parsed,
      "invalid value 'nope' for '--value <V>' from environment variable TOOL_VALUE: expected a whole number from 0 to 281474976710655",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--flag", "Flag", [Cli.env("TOOL_FLAG")]),
  ]), Cli.host_var(host(), "TOOL_FLAG", "maybe"), []) ==
    failed(Parsed,
      "invalid value 'maybe' for '--flag' from environment variable TOOL_FLAG: expected true or false",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_src_env_names_eval:
  {ran(env_chain(), Cli.host_var(host(), "LEGACY_OUT", "old"), []) ==
    went([
      field("out", ["old"], Cli.Env{}),
    ]) : Cli.Step<Parsed>} &
  {ran(env_chain(), Cli.host_var(host(), "LEGACY_N", "nope"), []) ==
    failed(Parsed,
      "invalid value 'nope' for '--n <N>' from environment variable LEGACY_N: expected a whole number from 0 to 281474976710655",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_rel_required_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--out <O>", "Output", [Cli.required()]),
    Cli.arg("<FILE>", "File", []),
    Cli.arg("--ok", "Ready", []),
  ]), host(), ["--ok"]) ==
    failed(Parsed,
      "the following required arguments were not provided:\n  --out <O>\n  <FILE>",
      [], "tool [OPTIONS] --out <O> <FILE>") : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--out <O>", "Output", [Cli.required(), Cli.env("TOOL_OUT")]),
  ]), Cli.host_var(host(), "TOOL_OUT", "env"), []) ==
    went([
      field("out", ["env"], Cli.Env{}),
    ]) : Cli.Step<Parsed>}

law g_rel_need_one_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.need_one("pick"),
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
  ]), host(), ["--help"]) ==
    Cli.Quit{0, page([
      "Tool",
      "",
      "Usage: tool [OPTIONS] <--a|--b>",
      "",
      "Options:",
      "      --a     A",
      "      --b     B",
      "  -h, --help  Print help",
    ]), ""} : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.need_one("pick"),
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
  ]), host(), ["--", "x"]) ==
    failed(Parsed, "unexpected argument 'x' found",
      [], "tool [OPTIONS] <--a|--b>") : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.need_one("pick"),
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
    Cli.arg("--ok", "Ready", []),
  ]), host(), ["--ok"]) ==
    failed(Parsed,
      "the following required arguments were not provided:\n  <--a|--b>",
      [], "tool [OPTIONS] <--a|--b>") : Cli.Step<Parsed>}

law g_rel_exclusive_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.exclusive("pick"),
    Cli.arg("--a", "A", [Cli.group("pick")]),
    Cli.arg("--b", "B", [Cli.group("pick")]),
  ]), host(), ["--a", "--b"]) ==
    failed(Parsed, "the argument '--b' cannot be used with '--a'",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_rel_conflict_order_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--a <A>", "A", [Cli.env("TOOL_A"), Cli.conflicts("b")]),
    Cli.arg("--b <B>", "B", []),
  ]), Cli.host_var(host(), "TOOL_A", "env"), ["--b=argv"]) ==
    failed(Parsed, "the argument '--a <A>' cannot be used with '--b <B>'",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.conflicts("b")]),
    Cli.arg("--b", "B", []),
  ]), host(), ["--b", "--a"]) ==
    failed(Parsed, "the argument '--a' cannot be used with '--b'",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_rel_requires_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.requires("b")]),
    Cli.arg("--b <B>", "B", [Cli.env("TOOL_B")]),
  ]), host(), ["--a"]) ==
    failed(Parsed, "the argument '--a' requires '--b <B>'",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.requires("b")]),
    Cli.arg("--b <B>", "B", [Cli.env("TOOL_B")]),
  ]), Cli.host_var(host(), "TOOL_B", "env"), ["--a"]) ==
    went([
      field("a", ["true"], Cli.Argv{}),
      field("b", ["env"], Cli.Env{}),
    ]) : Cli.Step<Parsed>}

law g_rel_defaults_eval:
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--a <A>", "A", [Cli.default("a"), Cli.conflicts("b")]),
    Cli.arg("--b <B>", "B", [Cli.default("b")]),
  ]), host(), ["--b=argv"]) ==
    went([
      field("a", ["a"], Cli.Default{}),
      field("b", ["argv"], Cli.Argv{}),
    ]) : Cli.Step<Parsed>} &
  {ran(Cli.cmd("tool", "Tool", [
    Cli.arg("--a", "A", [Cli.requires("b")]),
    Cli.arg("--b <B>", "B", [Cli.default("b")]),
  ]), host(), ["--a"]) ==
    failed(Parsed, "the argument '--a' requires '--b <B>'",
      [], "tool [OPTIONS]") : Cli.Step<Parsed>}

law g_rel_global_groups_eval:
  {ran(fmt_tool(), host(), ["--out", "x", "run"]) ==
    failed(Parsed,
      "the following required arguments were not provided:\n  <--json|--yaml>",
      [], "tool run [OPTIONS] --out <X> <--json|--yaml> [COMMAND]")
    : Cli.Step<Parsed>} &
  {ran(fmt_tool(), host(), ["--out", "x", "--json", "run", "--yaml"]) ==
    failed(Parsed, "the argument '--yaml' cannot be used with '--json'",
      [], "tool run [OPTIONS] --out <X> <--json|--yaml> [COMMAND]")
    : Cli.Step<Parsed>} &
  {ran(fmt_tool(), host(), ["--out", "x", "conv"]) ==
    failed(Parsed,
      "the following required arguments were not provided:\n  <--json|--yaml|--toml>",
      [], "tool conv [OPTIONS] --out <X> <--json|--yaml|--toml>")
    : Cli.Step<Parsed>} &
  {ran(fmt_tool(), host(), ["run", "deep", "--yaml", "--out", "x"]) ==
    went_to(["run", "deep"], [
      field("yaml", ["true"], Cli.Argv{}),
      field("out", ["x"], Cli.Argv{}),
    ], None{}) : Cli.Step<Parsed>}

# G-ERR E12: a decoder's Usage fault is an error at the matched scope, exit
# 2, colored by stderr's decision; Bug prints `bug: <msg>` uncolored, exit
# 70; Done is Go with term's decisions and the host width, unclamped.
# Messages print as given: a Usage message's final newline adds a blank
# line before the usage, and a Bug message's makes the output end in two.
def strict() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.sub_optional(),
    Cli.arg("--ok", "Accept", [Cli.global()]),
    Cli.arg("--bug", "Fail as a defect", [Cli.global()]),
    Cli.sub("deep", "Deep", []),
  ])

# Each fault's message ends with end.
def verdict(bug: Bool, ok: Bool, end: String) -> Cli.Dec(String):
  match bug ok:
    case True{} _: Cli.bug(String, String.append("--bug was given", end))
    case False{} True{}: Done{"accepted"}
    case False{} False{}:
      Cli.fail(String, String.append("pass --ok to accept", end))

def strict_decode(+m: Cli.Matches) -> Cli.Dec(String):
  do Cli.Dec<String>:
    ok : Bool <- Cli.flag(m, "ok")
    bug : Bool <- Cli.flag(m, "bug")
    answer : String <- verdict(bug, ok, "")
    return answer

def strict_run(h: Cli.Host, argv: List<&2, String>) -> Cli.Step<String>:
  Cli.eval(~String, ~strict_decode, strict(), h, argv)

def newline_decode(+m: Cli.Matches) -> Cli.Dec(String):
  do Cli.Dec<String>:
    ok : Bool <- Cli.flag(m, "ok")
    bug : Bool <- Cli.flag(m, "bug")
    answer : String <- verdict(bug, ok, "\n")
    return answer

def newline_run(argv: List<&2, String>) -> Cli.Step<String>:
  Cli.eval(~String, ~newline_decode, strict(), host(), argv)

law g_err_decode:
  {strict_run(host(), []) ==
    failed(String, "pass --ok to accept", [], "tool [OPTIONS] [COMMAND]")
    : Cli.Step<String>} &
  {strict_run(host(), ["deep"]) ==
    failed(String, "pass --ok to accept", [], "tool deep [OPTIONS]")
    : Cli.Step<String>} &
  {strict_run(Cli.host_tty(host(), False{}, True{}), []) ==
    Cli.Quit{2, "", page([
      "\u{1B}[1;31merror:\u{1B}[0m pass --ok to accept",
      "",
      "\u{1B}[1;4mUsage:\u{1B}[0m \u{1B}[1mtool\u{1B}[0m [OPTIONS] [COMMAND]",
      "",
      "For more information, try '\u{1B}[1m--help\u{1B}[0m'.",
    ])} : Cli.Step<String>} &
  {strict_run(host(), ["--ok", "deep", "--bug"]) ==
    Cli.Quit{70, "", "bug: --bug was given\n"} : Cli.Step<String>} &
  {strict_run(tty(), ["--bug"]) ==
    Cli.Quit{70, "", "bug: --bug was given\n"} : Cli.Step<String>} &
  {strict_run(host(), ["deep", "--ok"]) ==
    Cli.Go{"accepted", Cli.Term{False{}, False{}, 80n}} : Cli.Step<String>} &
  {strict_run(Cli.host_tty(Cli.host(200n), True{}, False{}), ["--ok"]) ==
    Cli.Go{"accepted", Cli.Term{True{}, False{}, 200n}} : Cli.Step<String>} &
  {Cli.eval(~Demo.Action, ~Demo.decode, Demo.cli(), tty(),
    ["--color=never", "list"]) ==
    Cli.Go{Demo.Action{0n, None{}, Demo.Show{False{}, Demo.Plain{}}},
      Cli.Term{False{}, False{}, 80n}} : Cli.Step<Demo.Action>} &
  {newline_run([]) == Cli.Quit{2, "", page([
    "error: pass --ok to accept",
    "",
    "",
    "Usage: tool [OPTIONS] [COMMAND]",
    "",
    "For more information, try '--help'.",
  ])} : Cli.Step<String>} &
  {newline_run(["--bug"]) ==
    Cli.Quit{70, "", "bug: --bug was given\n\n"} : Cli.Step<String>}

# G-ERR: a root's usage_status(n) ends each of eval's usage errors with n,
# with the text it has without one: a scan error at the root or in a
# subcommand, the summary of a root that needs a subcommand, and a decoder's
# Usage fault. Help still exits 0, and a decoder's Bug and a lint failure
# 70. usage_code is the root's first usage_status when its code is from 1
# to 255, else 2; one on a subcommand or an arg is not the root's.
def coded(items: List<&2, Cli.Item>) -> Cli.Cmd:
  Cli.cmd("tool", "Tool", List.append(&2, Cli.Item, items, [
    Cli.arg("--ok", "Accept", [Cli.global()]),
    Cli.arg("--bug", "Fail as a defect", [Cli.global()]),
    Cli.sub("deep", "Deep", []),
  ]))

def coded_run(items: List<&2, Cli.Item>,
    argv: List<&2, String>) -> Cli.Step<String>:
  Cli.eval(~String, ~strict_decode, coded(items), host(), argv)

law g_err_status:
  {Cli.usage_code(coded([])) == 2 : U32} &
  {Cli.usage_code(coded([Cli.usage_status(125)])) == 125 : U32} &
  {Cli.usage_code(coded([Cli.usage_status(1), Cli.usage_status(125)])) == 1
    : U32} &
  {Cli.usage_code(coded([Cli.usage_status(255)])) == 255 : U32} &
  {Cli.usage_code(coded([Cli.usage_status(0)])) == 2 : U32} &
  {Cli.usage_code(coded([Cli.usage_status(256), Cli.usage_status(125)]))
    == 2 : U32} &
  {Cli.usage_code(Cli.cmd("tool", "Tool", [
    Cli.sub("deep", "Deep", [Cli.usage_status(125)]),
  ])) == 2 : U32} &
  {Cli.usage_code(Cli.cmd("tool", "Tool", [
    Cli.arg("--ok", "Accept", [Cli.usage_status(125)]),
  ])) == 2 : U32} &
  {coded_run([Cli.usage_status(125)], []) == Cli.Quit{125, "", page([
    "Tool",
    "",
    "Usage: tool [OPTIONS] <COMMAND>",
    "",
    "Commands:",
    "  deep        Deep",
    "  help        Print this message or the help of the given subcommand(s)",
    "",
    "Options:",
    "      --ok    Accept",
    "      --bug   Fail as a defect",
    "  -h, --help  Print help",
  ])} : Cli.Step<String>} &
  {coded_run([Cli.usage_status(125)], ["--bogus"]) ==
    Cli.Quit{125, "", error_text("unexpected argument '--bogus' found", [],
      "tool [OPTIONS] <COMMAND>")} : Cli.Step<String>} &
  {coded_run([Cli.usage_status(125)], ["deep", "--bogus"]) ==
    Cli.Quit{125, "", error_text("unexpected argument '--bogus' found", [],
      "tool deep [OPTIONS]")} : Cli.Step<String>} &
  {coded_run([Cli.usage_status(125)], ["deep"]) ==
    Cli.Quit{125, "", error_text("pass --ok to accept", [],
      "tool deep [OPTIONS]")} : Cli.Step<String>} &
  {coded_run([Cli.usage_status(125)], ["deep", "--bug"]) ==
    Cli.Quit{70, "", "bug: --bug was given\n"} : Cli.Step<String>} &
  {coded_run([Cli.usage_status(125)], ["deep", "--ok"]) ==
    Cli.Go{"accepted", Cli.Term{False{}, False{}, 80n}} : Cli.Step<String>} &
  {coded_run([Cli.usage_status(125)], ["deep", "-h"]) == Cli.Quit{0, page([
    "Deep",
    "",
    "Usage: tool deep [OPTIONS]",
    "",
    "Options:",
    "      --ok    Accept",
    "      --bug   Fail as a defect",
    "  -h, --help  Print help",
  ]), ""} : Cli.Step<String>} &
  {coded_run([Cli.usage_status(0)], ["--bogus"]) == Cli.Quit{70, "", page([
    "bug: invalid command-line definition",
    "  tool: usage_status(0) is not an exit status from 1 to 255",
  ])} : Cli.Step<String>}

# G-LINT: lint comes before every rule, so a bad spec exits 70 even for
# --help, --version or empty argv; the text is never colored.
def broken() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.version("1.0"),
    Cli.arg("--help", "Help", []),
    Cli.sub("run", "Run", [
      Cli.arg("-v", "Verbose", []),
      Cli.arg("-v", "Verbose again", []),
    ]),
  ])

def broken_exit() -> Cli.Step<Parsed>:
  Cli.Quit{70, "", page([
    "bug: invalid command-line definition",
    "  tool: '--help' is reserved",
    "  tool run: '-v' is declared more than once",
  ])}

law g_lint_exit:
  {ran(broken(), host(), ["--help"]) == broken_exit() : Cli.Step<Parsed>} &
  {ran(broken(), host(), ["--version"]) == broken_exit()
    : Cli.Step<Parsed>} &
  {ran(broken(), host(), []) == broken_exit() : Cli.Step<Parsed>} &
  {ran(broken(), tty(), ["run", "-v"]) == broken_exit() : Cli.Step<Parsed>}

# G-LINT: a required() that descent drops stops eval before any rule, with
# or without the subcommand or the option in argv.
def dead_required_exit() -> Cli.Step<Parsed>:
  Cli.Quit{70, "", page([
    "bug: invalid command-line definition",
    "  tool: 'required' is not allowed here",
  ])}

law g_lint_required_sub_eval:
  {ran(parent_required([Cli.required()], []), host(), ["run"])
    == dead_required_exit() : Cli.Step<Parsed>} &
  {ran(parent_required([Cli.required()], []), host(), ["--out", "x", "run"])
    == dead_required_exit() : Cli.Step<Parsed>} &
  {ran(parent_required([Cli.required()], []), host(), [])
    == dead_required_exit() : Cli.Step<Parsed>}

# §6.7: the variables Run.host reads: each arg's env name in pre-order,
# then the color and width names, keeping only the first of any repeat.
def envs() -> Cli.Cmd:
  Cli.cmd("tool", "Tool", [
    Cli.arg("--a <A>", "A", [Cli.env("B_VAR")]),
    Cli.sub("x", "X", [
      Cli.arg("--c <C>", "C", [Cli.env("A_VAR")]),
      Cli.arg("--d <D>", "D", [Cli.env("B_VAR"), Cli.hidden()]),
    ]),
    Cli.arg("--e <E>", "E", [Cli.env("TERM"), Cli.global()]),
  ])

law g_vars:
  {Cli.vars(Demo.cli()) == ["PKG_REGISTRY", "NO_COLOR", "CLICOLOR",
    "CLICOLOR_FORCE", "TERM", "COLUMNS"] : List<&2, String>} &
  {Cli.vars(envs()) == ["B_VAR", "A_VAR", "TERM", "NO_COLOR", "CLICOLOR",
    "CLICOLOR_FORCE", "COLUMNS"] : List<&2, String>} &
  {Cli.vars(flags()) == ["NO_COLOR", "CLICOLOR", "CLICOLOR_FORCE", "TERM",
    "COLUMNS"] : List<&2, String>}

# §6.7: every name an arg lists, in order; a repeat is kept once.
law g_vars_env_names:
  {Cli.vars(env_chain()) == ["TOOL_OUT", "LEGACY_OUT", "TOOL_N", "LEGACY_N",
    "NO_COLOR", "CLICOLOR", "CLICOLOR_FORCE", "TERM", "COLUMNS"]
    : List<&2, String>} &
  {Cli.vars(Cli.cmd("tool", "Tool", [
    Cli.arg("--a <A>", "A", [Cli.env("A_VAR"), Cli.env("TERM"),
      Cli.env("A_VAR")]),
  ])) == ["A_VAR", "TERM", "NO_COLOR", "CLICOLOR", "CLICOLOR_FORCE",
    "COLUMNS"] : List<&2, String>}

# §7.3: the host from what Run.host reads: variables, then whether stdout
# and stderr are TTYs, then their columns. COLUMNS sets the width when
# as_nat accepts it and it is at least 1, so past U32 but not past
# 281474976710655; otherwise stdout's columns if it is a TTY, else stderr's
# if it is one; 0 or no TTY gives 80. The checker's Nat is unary, so a width
# past U32 is stated as Nat.read's answer, which as_nat uses (§8.5), not as
# a literal it would have to build.
def width_of(h: Cli.Host) -> Nat:
  match h:
    case Cli.Host{width, vars, out_tty, err_tty}: width

def columns(value: String) -> List<&2, Cli.Var>:
  [Cli.Var{"COLUMNS", value}]

law g_host_probe:
  {Cli.probe([Cli.Var{"TERM", "xterm"}, Cli.Var{"COLUMNS", "120"}],
    True{}, False{}, 90, 70) == Cli.Host{120n,
    [Cli.Var{"TERM", "xterm"}, Cli.Var{"COLUMNS", "120"}], True{}, False{}}
    : Cli.Host} &
  {width_of(Cli.probe(columns("1"), False{}, False{}, 0, 0)) == 1n : Nat} &
  {width_of(Cli.probe(columns("4294967296"), False{}, False{}, 0, 0))
    == Maybe.default(&2, Nat, Nat.read("4294967296"), 0n) : Nat} &
  {width_of(Cli.probe(columns("281474976710656"), True{}, True{}, 90, 70))
    == 90n : Nat} &
  {width_of(Cli.probe(columns("0"), True{}, True{}, 90, 70)) == 90n : Nat} &
  {width_of(Cli.probe(columns("wide"), True{}, True{}, 90, 70)) == 90n
    : Nat} &
  {width_of(Cli.probe(columns(""), True{}, True{}, 90, 70)) == 90n : Nat} &
  {width_of(Cli.probe([], True{}, True{}, 90, 70)) == 90n : Nat} &
  {width_of(Cli.probe([], True{}, True{}, 0, 70)) == 80n : Nat} &
  {width_of(Cli.probe([], False{}, True{}, 90, 70)) == 70n : Nat} &
  {width_of(Cli.probe([], False{}, True{}, 90, 0)) == 80n : Nat} &
  {width_of(Cli.probe([], False{}, False{}, 90, 70)) == 80n : Nat}

# §7.2: act's code passes through up to 255; a larger one exits 70 with a
# bug line for stderr.
law g_act_exit:
  {Cli.act_exit(0) == (0, "") : (U32 & String)} &
  {Cli.act_exit(1) == (1, "") : (U32 & String)} &
  {Cli.act_exit(255) == (255, "") : (U32 & String)} &
  {Cli.act_exit(256) ==
    (70, "bug: exit code 256 is out of range 0..255\n") : (U32 & String)} &
  {Cli.act_exit(4294967295) ==
    (70, "bug: exit code 4294967295 is out of range 0..255\n")
    : (U32 & String)}

# §12.3: pkg's plan gives the line its run prints and its code. The line is
# the job, its fields, verbose and any -C dir, with lists joined by commas;
# `run exit <N>` with one argument that reads as a U32 returns N, and every
# other action returns 0.
def job(j: Demo.Job) -> Demo.Action:
  Demo.Action{0n, None{}, j}

law g_plan_pkg:
  {Demo.plan(job(Demo.Add{True{}, "https://registry.example",
    ["left-pad", "lodash"]})) == Demo.Plan{0,
    "add dev=true registry=https://registry.example names=left-pad,lodash verbose=0"}
    : Demo.Plan} &
  {Demo.plan(Demo.Action{2n, Some{"/tmp"}, Demo.Remove{["a"]}}) ==
    Demo.Plan{0, "remove names=a verbose=2 dir=/tmp"} : Demo.Plan} &
  {Demo.plan(job(Demo.Show{False{}, Demo.Json{}})) ==
    Demo.Plan{0, "list all=false format=json verbose=0"} : Demo.Plan} &
  {Demo.plan(job(Demo.Script{"build", ["x", "--", "-y"]})) ==
    Demo.Plan{0, "run script=build args=x,--,-y verbose=0"} : Demo.Plan} &
  {Demo.plan(job(Demo.Script{"exit", ["3"]})) ==
    Demo.Plan{3, "run script=exit args=3 verbose=0"} : Demo.Plan} &
  {Demo.plan(job(Demo.Script{"exit", ["256"]})) ==
    Demo.Plan{256, "run script=exit args=256 verbose=0"} : Demo.Plan} &
  {Demo.plan(job(Demo.Script{"exit", ["x"]})) ==
    Demo.Plan{0, "run script=exit args=x verbose=0"} : Demo.Plan} &
  {Demo.plan(job(Demo.Script{"exit", ["1", "2"]})) ==
    Demo.Plan{0, "run script=exit args=1,2 verbose=0"} : Demo.Plan} &
  {Demo.plan(job(Demo.Script{"exit", []})) ==
    Demo.Plan{0, "run script=exit args= verbose=0"} : Demo.Plan}

# pkg's run on argv, with an 80-column host and no variables or terminal.
def pkg_invoked(argv: List<&2, String>) -> Cli.Ran:
  Cli.invoke(~Demo.Action, ~Demo.decode, ~Demo.ran, Demo.cli(), Cli.host(80n),
    argv)

# §7.2: Cli.invoke gives what Run.planned writes and exits with. A run that
# eval ends gives Quit's code and text; one that reaches the plan gives the
# plan's, with act_exit's mapping, so `run exit 256` exits 70 with the bug
# line on stderr. pkg's plan puts its line on stdout and nothing on stderr.
law g_invoke_pkg:
  {pkg_invoked(["run", "exit", "3"]) ==
    Cli.Ran{3, "run script=exit args=3 verbose=0\n", ""} : Cli.Ran} &
  {pkg_invoked(["run", "exit", "256"]) ==
    Cli.Ran{70, "run script=exit args=256 verbose=0\n",
      "bug: exit code 256 is out of range 0..255\n"} : Cli.Ran} &
  {pkg_invoked(["--version"]) == Cli.Ran{0, "pkg 0.1.0\n", ""} : Cli.Ran} &
  {pkg_invoked(["list", "-x"]) == Cli.Ran{2, "", String.concat([
    "error: unexpected argument '-x' found\n",
    "\n",
    "Usage: pkg list [OPTIONS]\n",
    "\n",
    "For more information, try '--help'.\n",
  ])} : Cli.Ran}

# A plan that writes both streams, for g_invoke_plan: pkg's line and the
# terminal's width on stdout, and a run job's arguments on stderr, joined
# by "\n" with none after the last.
def noisy_err(j: Demo.Job) -> String:
  match j:
    case Demo.Add{dev, registry, names}: ""
    case Demo.Remove{names}: ""
    case Demo.Show{all, format}: ""
    case Demo.Script{name, args}: String.join(args, "\n")

def noisy_ran(p: Demo.Plan, t: Cli.Term, err: String) -> Cli.Ran:
  match p t:
    case Demo.Plan{code, line} Cli.Term{out_color, err_color, width}:
      Cli.Ran{code, String.concat([line, " width=", Nat.show(width), "\n"]),
        err}

def noisy_action(+a: Demo.Action, t: Cli.Term) -> Cli.Ran:
  match a:
    case Demo.Action{verbose, dir, job}:
      noisy_ran(Demo.plan(a), t, noisy_err(job))

def noisy(+t: Cli.Term, a: Demo.Action) -> Cli.Ran:
  noisy_action(a, t)

# The noisy plan's run on argv, with a 60-column host.
def noisy_invoked(argv: List<&2, String>) -> Cli.Ran:
  Cli.invoke(~Demo.Action, ~Demo.decode, ~noisy, Demo.cli(), Cli.host(60n),
    argv)

# §7.2: invoke hands the plan the host's terminal and keeps the plan's
# stderr, ending it in "\n", as IO.print_err does, unless it is empty or
# already ends so; act_exit's bug line comes after it.
law g_invoke_plan:
  {noisy_invoked(["run", "exit", "256"]) ==
    Cli.Ran{70, "run script=exit args=256 verbose=0 width=60\n",
      "256\nbug: exit code 256 is out of range 0..255\n"} : Cli.Ran} &
  {noisy_invoked(["-v", "run", "x", "a", "b"]) ==
    Cli.Ran{0, "run script=x args=a,b verbose=1 width=60\n", "a\nb\n"}
    : Cli.Ran} &
  {noisy_invoked(["run", "x", "a", ""]) ==
    Cli.Ran{0, "run script=x args=a, verbose=0 width=60\n", "a\n"}
    : Cli.Ran} &
  {noisy_invoked(["run", "x"]) ==
    Cli.Ran{0, "run script=x args= verbose=0 width=60\n", ""} : Cli.Ran}

# ---- M6: completions and man pages (§11) ----

# The models below say how a reader takes the quoters' output back. Each
# reads only what the quoters need, and answers None for anything else: an
# open quote, a char the reader would treat specially, or an escape it does
# not define. None says only that the model does not read the text.
def put(c: Char, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case Some{s}: Some{SCon{c, s}}
    case None{}: None{}

def put_if(ok: Bool, c: Char, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}: put(c, m)
    case False{}: None{}

# An ASCII letter or digit, or a char of extra.
def plain_char(+c: Char, extra: String) -> Bool:
  Bool.or(Bool.or(Char.is_alpha(c), Char.is_digit(c)),
    String.contains(extra, Char.show(c)))

# A POSIX shell reading one word (XCU 2.2): in '…' every char stands for
# itself; outside, \ newline is removed, \c gives c, and a plain char or
# one of _@%+=:,./- stands for itself.
def sh_read(s: String, quoted: Bool) -> Maybe<&2, String>:
  match s quoted:
    case SNil{} False{}: Some{""}
    case SNil{} True{}: None{}
    case SCon{Chr{39}, tail} q: sh_read(tail, Bool.not(q))
    case SCon{c, tail} True{}: put(c, sh_read(tail, True{}))
    case SCon{Chr{92}, SCon{Chr{10}, tail}} False{}: sh_read(tail, False{})
    case SCon{Chr{92}, SCon{c, tail}} False{}: put(c, sh_read(tail, False{}))
    case SCon{Chr{92}, SNil{}} False{}: None{}
    case SCon{+c, tail} False{}:
      put_if(plain_char(c, "_@%+=:,./-"), c, sh_read(tail, False{}))

def Sh.unquote(s: String) -> Maybe<&2, String>:
  sh_read(s, False{})

# fish reading one word: in '…', \\ gives \, \' gives ', and every other
# char, \ included, stands for itself; outside, a plain char or one of
# _@+=:,./- stands for itself.
def fish_read(s: String, quoted: Bool) -> Maybe<&2, String>:
  match s quoted:
    case SNil{} False{}: Some{""}
    case SNil{} True{}: None{}
    case SCon{Chr{39}, tail} q: fish_read(tail, Bool.not(q))
    case SCon{Chr{92}, SCon{Chr{92}, tail}} True{}:
      put(Chr{92}, fish_read(tail, True{}))
    case SCon{Chr{92}, SCon{Chr{39}, tail}} True{}:
      put(Chr{39}, fish_read(tail, True{}))
    case SCon{c, tail} True{}: put(c, fish_read(tail, True{}))
    case SCon{+c, tail} False{}:
      put_if(plain_char(c, "_@+=:,./-"), c, fish_read(tail, False{}))

def Fish.unquote(s: String) -> Maybe<&2, String>:
  fish_read(s, False{})

# zsh's _arguments reading the text of a spec field: \c gives c, and an
# unescaped [, ] or : would end the field.
def Zsh.unesc(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}: Some{""}
    case SCon{Chr{92}, SCon{c, tail}}: put(c, Zsh.unesc(tail))
    case SCon{Chr{92}, SNil{}}: None{}
    case SCon{Chr{91}, tail}: None{}
    case SCon{Chr{93}, tail}: None{}
    case SCon{Chr{58}, tail}: None{}
    case SCon{c, tail}: put(c, Zsh.unesc(tail))

# man(7) reading text lines: \e, \-, \(dq, \(aq and \(ga give \, -, ", '
# and `, and \& gives nothing. A line may not start with . or ' (a request)
# or a space (a break). A raw -, ", ' or ` is None, since groff may typeset
# it as a hyphen or a curly quote, and so is any other escape.
def roff_read(s: String, start: Bool) -> Maybe<&2, String>:
  match s start:
    case SNil{} _: Some{""}
    case SCon{Chr{46}, tail} True{}: None{}
    case SCon{Chr{32}, tail} True{}: None{}
    case SCon{Chr{10}, tail} _: put(Chr{10}, roff_read(tail, True{}))
    case SCon{Chr{92}, SCon{Chr{101}, tail}} _:
      put(Chr{92}, roff_read(tail, False{}))
    case SCon{Chr{92}, SCon{Chr{45}, tail}} _:
      put(Chr{45}, roff_read(tail, False{}))
    case SCon{Chr{92}, SCon{Chr{38}, tail}} _: roff_read(tail, False{})
    case SCon{Chr{92}, SCon{Chr{40}, SCon{Chr{100}, SCon{Chr{113}, tail}}}} _:
      put(Chr{34}, roff_read(tail, False{}))
    case SCon{Chr{92}, SCon{Chr{40}, SCon{Chr{97}, SCon{Chr{113}, tail}}}} _:
      put(Chr{39}, roff_read(tail, False{}))
    case SCon{Chr{92}, SCon{Chr{40}, SCon{Chr{103}, SCon{Chr{97}, tail}}}} _:
      put(Chr{96}, roff_read(tail, False{}))
    case SCon{Chr{92}, tail} _: None{}
    case SCon{Chr{45}, tail} _: None{}
    case SCon{Chr{34}, tail} _: None{}
    case SCon{Chr{39}, tail} _: None{}
    case SCon{Chr{96}, tail} _: None{}
    case SCon{c, tail} _: put(c, roff_read(tail, False{}))

def Roff.unesc(s: String) -> Maybe<&2, String>:
  roff_read(s, True{})

# P3: a POSIX shell reads Sh.quote(s) as the one word s.
law p3:
  for +s: String
  {Sh.unquote(Cli.Sh.quote(s)) == Some{s} : Maybe<&2, String>}

# P4: fish reads Fish.quote(s) as the one word s.
law p4:
  for +s: String
  {Fish.unquote(Cli.Fish.quote(s)) == Some{s} : Maybe<&2, String>}

# P5: _arguments reads Zsh.esc(s) as s, so it holds no unescaped [, ] or :.
law p5:
  for +s: String
  {Zsh.unesc(Cli.Zsh.esc(s)) == Some{s} : Maybe<&2, String>}

# P6: no line of Roff.esc(s) starts with . or ', so none is a request.
def no_request(s: String, start: Bool) -> Bool:
  match s start:
    case SNil{} _: True{}
    case SCon{Chr{46}, tail} True{}: False{}
    case SCon{Chr{39}, tail} True{}: False{}
    case SCon{Chr{10}, tail} _: no_request(tail, True{})
    case SCon{c, tail} _: no_request(tail, False{})

law p6:
  for s: String
  {no_request(Cli.Roff.esc(s), True{}) == True{} : Bool}

# P15: man(7) reads Roff.esc(s) as s.
law p15:
  for +s: String
  {Roff.unesc(Cli.Roff.esc(s)) == Some{s} : Maybe<&2, String>}

# The models read what each reader would, and refuse what it would read
# differently.
law g_quote_models:
  {Sh.unquote("a'b c'\\'d\\\ne") == Some{"ab c'de"} : Maybe<&2, String>} &
  {Sh.unquote("a b") == None{} : Maybe<&2, String>} &
  {Sh.unquote("$x") == None{} : Maybe<&2, String>} &
  {Sh.unquote("'a") == None{} : Maybe<&2, String>} &
  {Fish.unquote("'a\\b\\\\\\''") == Some{"a\\b\\'"} : Maybe<&2, String>} &
  {Fish.unquote("a\\ b") == None{} : Maybe<&2, String>} &
  {Fish.unquote("%self") == None{} : Maybe<&2, String>} &
  {Zsh.unesc("a\\:b\\\\") == Some{"a:b\\"} : Maybe<&2, String>} &
  {Zsh.unesc("a:b") == None{} : Maybe<&2, String>} &
  {Zsh.unesc("a\\") == None{} : Maybe<&2, String>} &
  {Roff.unesc("\\&.a \\- \\e\\(dq\n\\& b") == Some{".a - \\\"\n b"}
    : Maybe<&2, String>} &
  {Roff.unesc("a-b") == None{} : Maybe<&2, String>} &
  {Roff.unesc("a\n.b") == None{} : Maybe<&2, String>} &
  {Roff.unesc("\\fBa\\fR") == None{} : Maybe<&2, String>}

# §11: the quoters' bytes. Roff.esc escapes every \, -, ", ' and `, and
# puts \& before a line that starts with . or a space.
law g_quote:
  {Cli.Sh.quote("it's") == "'it'\\''s'" : String} &
  {Cli.Sh.quote("") == "''" : String} &
  {Cli.Fish.quote("it's a\\b") == "'it\\'s a\\\\b'" : String} &
  {Cli.Zsh.esc("a:[b]\\c") == "a\\:\\[b\\]\\\\c" : String} &
  {Cli.Roff.esc(".x-y \"q\" `b` \\\n'z\n c") ==
    "\\&.x\\-y \\(dqq\\(dq \\(gab\\(ga \\e\n\\(aqz\n\\& c" : String}

# The engine every bash script shares, for function prefix id, then
# the line that binds it to name, already quoted.
def bash_rest(+id: String, name: String) -> List<&2, String>:
  [
    "",
    "# Offers each value of kind that starts with $1, written after $2 and cut to",
    "# the part readline completes: the text after the last \"=\" or \":\". Readline",
    "# quotes files and directories; words are quoted here.",
    String.concat([id, "_offer() {"]),
    "  local word full i",
    "  case $kind in",
    "    f) compopt -o filenames; mapfile -t values < <(compgen -f -- \"$1\") ;;",
    "    d) compopt -o filenames; mapfile -t values < <(compgen -d -- \"$1\") ;;",
    "    w)",
    "      for ((i = 0; i < ${#values[@]}; i++)); do",
    "        printf -v 'values[i]' %q \"${values[i]}\"",
    "      done ;;",
    "    *) return ;;",
    "  esac",
    "  for word in \"${values[@]}\"; do",
    "    full=$2$word",
    "    [[ $word == \"$1\"* ]] && COMPREPLY+=(\"${full:${#2}+${#1}-${#tail}}\")",
    "  done",
    "}",
    "",
    String.concat([id, "() {"]),
    "  local -a words=() opts=() subs=() dests=() values=()",
    "  local cur tail word line gap path= want= kind opt many rest i j n=0 end=0 help=0",
    "  COMPREPLY=()",
    "  # Rejoin the \"=\" and \":\" that bash splits words at. COMP_LINE has no blank",
    "  # at such a split, so a \"=\" typed as its own word stays one.",
    "  line=${COMP_LINE#*\"${COMP_WORDS[0]}\"}",
    "  for ((i = 1; i <= COMP_CWORD; i++)); do",
    "    word=${COMP_WORDS[i]}",
    "    tail=${COMP_WORDS[i-1]}",
    "    gap=${line%%[![:blank:]]*}",
    "    line=${line:${#gap}+${#word}}",
    "    if ((i > 1)) && [[ -z $gap ]] &&",
    "      [[ -n $word && -z ${word//[=:]} || -n $tail && -z ${tail//[=:]} ]]; then",
    "      words[${#words[@]}-1]+=$word",
    "    else",
    "      words+=(\"$word\")",
    "    fi",
    "  done",
    "  tail=${COMP_WORDS[COMP_CWORD]}",
    "  [[ -z ${tail//[=:]} ]] && tail=",
    "  cur=${words[${#words[@]}-1]}",
    "  unset 'words[${#words[@]}-1]'",
    String.concat(["  ", id, "_scope"]),
    "  for word in \"${words[@]}\"; do",
    "    if [[ -n $want ]]; then",
    "      want=",
    "    elif ((!end)) && [[ $word == -- ]]; then",
    "      end=1",
    "    elif ((!end)) && [[ $word == --* ]]; then",
    String.concat(["      ", id, "_arg \"${word%%=*}\""]),
    "      [[ -n $kind && $opt == 0 && $word != *=* ]] && want=$word",
    "    elif ((!end)) && [[ $word == -?* ]]; then",
    "      for ((j = 1; j < ${#word}; j++)); do",
    String.concat(["        ", id, "_arg \"-${word:j:1}\""]),
    "        [[ -n $kind ]] || continue",
    "        ((j + 1 == ${#word})) && want=-${word:j:1}",
    "        break",
    "      done",
    "    elif ((${#subs[@]})); then",
    "      ((end)) && return",
    "      if [[ $word == help ]] && ((!help)); then",
    "        help=1",
    "        continue",
    "      fi",
    "      for ((j = 0; j < ${#subs[@]}; j++)); do",
    "        [[ $word == \"${subs[j]}\" ]] && break",
    "      done",
    "      ((j < ${#subs[@]})) || return",
    "      path=${dests[j]}",
    String.concat(["      ", id, "_scope"]),
    "    else",
    "      # n counts the slots filled. The variadic slot stays open, but a rest()",
    "      # value takes every later word, so nothing more completes.",
    "      n=$((n + 1))",
    "      if ((n == many && rest)); then",
    "        end=1",
    "      elif ((n == many)); then",
    "        n=$((n - 1))",
    "      fi",
    "    fi",
    "  done",
    "  if [[ -n $want ]]; then",
    String.concat(["    ", id, "_arg \"$want\""]),
    String.concat(["    ", id, "_offer \"$cur\" ''"]),
    "  elif ((!end)) && [[ $cur == --*=* ]]; then",
    String.concat(["    ", id, "_arg \"${cur%%=*}\""]),
    String.concat(["    ", id, "_offer \"${cur#*=}\" \"${cur%%=*}=\""]),
    "  elif ((!end)) && [[ $cur == -* ]]; then",
    "    values=(\"${opts[@]}\") kind=w",
    "    ((help)) && values=('-h' '--help')",
    String.concat(["    ", id, "_offer \"$cur\" ''"]),
    "  elif ((!end && ${#subs[@]})); then",
    "    values=(\"${subs[@]}\") kind=w",
    "    ((help)) || values+=('help')",
    String.concat(["    ", id, "_offer \"$cur\" ''"]),
    "  elif ((!help)); then",
    String.concat(["    ", id, "_arg $((n + 1))"]),
    String.concat(["    ", id, "_offer \"$cur\" ''"]),
    "  fi",
    "}",
    "",
    String.concat(["complete -F ", id, " ", name]),
  ]

def pkg_bash() -> String:
  page(List.append(&2, String, [
    "# bash completion; needs bash 4 or later.",
    "",
    "# Sets the tables of command path $path: opts, the options to offer; subs and",
    "# dests, each subcommand name and the path it enters; many, the slot of the",
    "# variadic positional, or 0; rest, 1 when that slot is rest().",
    "_pkg_scope() {",
    "  opts=() subs=() dests=() many=0 rest=0",
    "  case $path in",
    "    '')",
    "      opts=('--color' '-v' '--verbose' '-C' '-h' '--help' '-V' '--version')",
    "      subs=('add' 'remove' 'rm' 'list' 'run' 'completions')",
    "      dests=('add' 'remove' 'remove' 'list' 'run' 'completions') ;;",
    "    'add')",
    "      opts=('-D' '--dev' '--registry' '--color' '-v' '--verbose' '-C' '-h' '--help')",
    "      many=1 rest=0 ;;",
    "    'remove')",
    "      opts=('--color' '-v' '--verbose' '-C' '-h' '--help')",
    "      many=1 rest=0 ;;",
    "    'list')",
    "      opts=('-a' '--all' '--format' '--color' '-v' '--verbose' '-C' '-h' '--help') ;;",
    "    'run')",
    "      opts=('--color' '-v' '--verbose' '-C' '-h' '--help')",
    "      many=2 rest=1 ;;",
    "    'completions')",
    "      opts=('--color' '-v' '--verbose' '-C' '-h' '--help') ;;",
    "  esac",
    "}",
    "",
    "# Sets kind to what the option or positional $1 (a name, or a 1-based slot)",
    "# takes at $path: w, a word from values; f, a file; d, a directory; s, other",
    "# text. kind is empty for an option that takes no value and for a positional",
    "# that completes nothing; opt is 1 when the value can only follow \"=\".",
    "_pkg_arg() {",
    "  kind= opt=0 values=()",
    "  case $path in",
    "    '')",
    "      case $1 in",
    "        '--color') kind=w values=('auto' 'always' 'never') ;;",
    "        '-C') kind=d ;;",
    "      esac ;;",
    "    'add')",
    "      case $1 in",
    "        '--registry') kind=s ;;",
    "        '--color') kind=w values=('auto' 'always' 'never') ;;",
    "        '-C') kind=d ;;",
    "      esac ;;",
    "    'remove')",
    "      case $1 in",
    "        '--color') kind=w values=('auto' 'always' 'never') ;;",
    "        '-C') kind=d ;;",
    "      esac ;;",
    "    'list')",
    "      case $1 in",
    "        '--format') kind=w values=('text' 'json') ;;",
    "        '--color') kind=w values=('auto' 'always' 'never') ;;",
    "        '-C') kind=d ;;",
    "      esac ;;",
    "    'run')",
    "      case $1 in",
    "        '--color') kind=w values=('auto' 'always' 'never') ;;",
    "        '-C') kind=d ;;",
    "      esac ;;",
    "    'completions')",
    "      case $1 in",
    "        '--color') kind=w values=('auto' 'always' 'never') ;;",
    "        '-C') kind=d ;;",
    "        1) kind=w values=('bash' 'zsh' 'fish') ;;",
    "      esac ;;",
    "  esac",
    "}",
  ], bash_rest("_pkg", "'pkg'")))

def quirks_bash() -> String:
  page(List.append(&2, String, [
    "# bash completion; needs bash 4 or later.",
    "",
    "# Sets the tables of command path $path: opts, the options to offer; subs and",
    "# dests, each subcommand name and the path it enters; many, the slot of the",
    "# variadic positional, or 0; rest, 1 when that slot is rest().",
    "_my_tool_scope() {",
    "  opts=() subs=() dests=() many=0 rest=0",
    "  case $path in",
    "    '')",
    "      opts=('-q' '--quiet' '--no-quiet' '--mode' '-o' '--out' '--output' '-h' '--help' '-V' '--version')",
    "      subs=('remote' 'rem')",
    "      dests=('remote' 'remote') ;;",
    "    'remote')",
    "      opts=('-q' '--quiet' '--no-quiet' '-h' '--help')",
    "      subs=('add')",
    "      dests=('remote add') ;;",
    "    'remote add')",
    "      opts=('-t' '--tag' '-q' '--quiet' '--no-quiet' '-h' '--help') ;;",
    "  esac",
    "}",
    "",
    "# Sets kind to what the option or positional $1 (a name, or a 1-based slot)",
    "# takes at $path: w, a word from values; f, a file; d, a directory; s, other",
    "# text. kind is empty for an option that takes no value and for a positional",
    "# that completes nothing; opt is 1 when the value can only follow \"=\".",
    "_my_tool_arg() {",
    "  kind= opt=0 values=()",
    "  case $path in",
    "    '')",
    "      case $1 in",
    "        '--mode') kind=w opt=1 values=('it'\\''s' 'a b' '$x' 'c:d' 'e\\f') ;;",
    "        '-o'|'--out'|'--output') kind=f ;;",
    "      esac ;;",
    "    'remote add')",
    "      case $1 in",
    "        '-t'|'--tag') kind=s ;;",
    "        2) kind=d ;;",
    "      esac ;;",
    "  esac",
    "}",
  ], bash_rest("_my_tool", "'my-tool'")))

def launch_bash() -> String:
  page(List.append(&2, String, [
    "# bash completion; needs bash 4 or later.",
    "",
    "# Sets the tables of command path $path: opts, the options to offer; subs and",
    "# dests, each subcommand name and the path it enters; many, the slot of the",
    "# variadic positional, or 0; rest, 1 when that slot is rest().",
    "_launch_scope() {",
    "  opts=() subs=() dests=() many=0 rest=0",
    "  case $path in",
    "    '')",
    "      opts=('-n' '--dry-run' '-h' '--help')",
    "      many=2 rest=1 ;;",
    "  esac",
    "}",
    "",
    "# Sets kind to what the option or positional $1 (a name, or a 1-based slot)",
    "# takes at $path: w, a word from values; f, a file; d, a directory; s, other",
    "# text. kind is empty for an option that takes no value and for a positional",
    "# that completes nothing; opt is 1 when the value can only follow \"=\".",
    "_launch_arg() {",
    "  kind= opt=0 values=()",
    "  case $path in",
    "    '')",
    "      case $1 in",
    "        1) kind=f ;;",
    "        2) kind=f ;;",
    "      esac ;;",
    "  esac",
    "}",
  ], bash_rest("_launch", "'launch'")))

# The function every fish script shares, for function prefix id.
def fish_is(+id: String) -> List<&2, String>:
  [
    "",
    "# Succeeds when the words before the cursor reach path $argv[1] and the next",
    "# word can be one of $argv[2..-1]: n, an option or subcommand; h, a",
    "# subcommand after help; v, an option's value; p<k>, positional slot k.",
    String.concat(["function ", id, "_is"]),
    "    # fish 4 deprecates -o, which fish 3 needs.",
    "    set -l words (commandline -xpc 2>/dev/null; or commandline -opc)",
    "    set -e words[1]",
    "    set -l path 0",
    String.concat(["    set -l shape (", id, "_shape 0 | string split ' ')"]),
    "    set -l want 0",
    "    set -l end 0",
    "    set -l help 0",
    "    set -l n 0",
    "    for word in $words",
    "        if test $want = 1",
    "            set want 0",
    "        else if test $end = 0; and test \"$word\" = --",
    "            set end 1",
    "        else if test $end = 0; and string match -q -r -- '^--.' $word",
    String.concat(["            if not string match -q -- '*=*' $word; and ", id, "_valued $path $word"]),
    "                set want 1",
    "            end",
    "        else if test $end = 0; and string match -q -r -- '^-.' $word",
    "            set -l chars (string split '' -- (string sub -s 2 -- $word))",
    "            for i in (seq (count $chars))",
    String.concat(["                if ", id, "_valued $path -$chars[$i]"]),
    "                    test $i = (count $chars); and set want 1",
    "                    break",
    "                end",
    "            end",
    "        else if test $shape[1] = 1",
    "            if test $end = 1",
    "                return 1",
    "            else if test $help = 0; and test \"$word\" = help",
    "                set help 1",
    "            else",
    String.concat(["                set path (", id, "_dest $path $word); or return 1"]),
    String.concat(["                set shape (", id, "_shape $path | string split ' ')"]),
    "            end",
    "        else",
    "            # n counts the slots filled. The variadic slot stays open, but a",
    "            # rest() value takes every later word, so nothing more completes.",
    "            set n (math $n + 1)",
    "            if test $n = $shape[2]; and test $shape[3] = 1",
    "                set end 1",
    "            else if test $n = $shape[2]",
    "                set n (math $n - 1)",
    "            end",
    "        end",
    "    end",
    "    test $path = $argv[1]; or return 1",
    "    set -l tags",
    "    if test $want = 1",
    "        set tags v",
    "    else",
    "        test $end = 0; and test $help = 0; and set -a tags n",
    "        test $end = 0; and test $help = 1; and set -a tags h",
    "        test $shape[1] = 0; and test $help = 0; and set -a tags p(math $n + 1)",
    "    end",
    "    for tag in $argv[2..-1]",
    "        contains -- $tag $tags; and return 0",
    "    end",
    "    return 1",
    "end",
  ]

def pkg_fish() -> String:
  page(List.concat(&2, String, [
    [
      "# fish completion; needs fish 3.3 or later.",
      "",
      "# Prints the number of the path that subcommand $argv[2] of path $argv[1]",
      "# enters; paths are numbered in pre-order from 0, the root.",
      "function __pkg_dest",
      "    switch \"$argv[1] $argv[2]\"",
      "        case '0 add'",
      "            echo 1",
      "        case '0 remove' '0 rm'",
      "            echo 2",
      "        case '0 list'",
      "            echo 3",
      "        case '0 run'",
      "            echo 4",
      "        case '0 completions'",
      "            echo 5",
      "        case '*'",
      "            return 1",
      "    end",
      "end",
      "",
      "# Succeeds when option $argv[2] takes the next word as its value at path",
      "# $argv[1].",
      "function __pkg_valued",
      "    switch $argv[1]",
      "        case 0",
      "            contains -- $argv[2] '--color' '-C'",
      "        case 1",
      "            contains -- $argv[2] '--registry' '--color' '-C'",
      "        case 2",
      "            contains -- $argv[2] '--color' '-C'",
      "        case 3",
      "            contains -- $argv[2] '--format' '--color' '-C'",
      "        case 4",
      "            contains -- $argv[2] '--color' '-C'",
      "        case 5",
      "            contains -- $argv[2] '--color' '-C'",
      "        case '*'",
      "            return 1",
      "    end",
      "end",
      "",
      "# Prints how path $argv[1] takes words: 1 if it has subcommands, else 0; the",
      "# slot of its variadic positional, or 0; 1 if that slot is rest(), else 0.",
      "function __pkg_shape",
      "    switch $argv[1]",
      "        case 0",
      "            echo 1 0 0",
      "        case 1",
      "            echo 0 1 0",
      "        case 2",
      "            echo 0 1 0",
      "        case 4",
      "            echo 0 2 1",
      "        case '*'",
      "            echo 0 0 0",
      "    end",
      "end",
      "",
      "# Prints the values of the one_of list numbered $argv[1].",
      "function __pkg_values",
      "    switch $argv[1]",
      "        case 1",
      "            printf '%s\\n' 'auto' 'always' 'never'",
      "        case 2",
      "            printf '%s\\n' 'text' 'json'",
      "        case 3",
      "            printf '%s\\n' 'bash' 'zsh' 'fish'",
      "    end",
      "end",
    ],
    fish_is("__pkg"),
    [
      "",
      "# Option lines also hold at v, so that fish can read grouped short options",
      "# before a value, as in -vC DIR.",
      "complete -c 'pkg' -f",
      "complete -c 'pkg' -n '__pkg_is 0 n v' -l 'color' -x -a '(__pkg_values 1)' -d 'When to use color'",
      "complete -c 'pkg' -n '__pkg_is 0 n v' -s 'v' -l 'verbose' -d 'More output; repeat for more'",
      "complete -c 'pkg' -n '__pkg_is 0 n v' -s 'C' -x -a '(__fish_complete_directories)' -d 'Run as if started in DIR'",
      "complete -c 'pkg' -n '__pkg_is 0 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'pkg' -n '__pkg_is 0 n' -s 'V' -l 'version' -d 'Print version'",
      "complete -c 'pkg' -n '__pkg_is 0 n h' -a 'add' -d 'Add packages'",
      "complete -c 'pkg' -n '__pkg_is 0 n h' -a 'remove' -d 'Remove packages'",
      "complete -c 'pkg' -n '__pkg_is 0 n h' -a 'rm' -d 'Remove packages'",
      "complete -c 'pkg' -n '__pkg_is 0 n h' -a 'list' -d 'List installed packages'",
      "complete -c 'pkg' -n '__pkg_is 0 n h' -a 'run' -d 'Run a package script'",
      "complete -c 'pkg' -n '__pkg_is 0 n h' -a 'completions' -d 'Print a shell completion script'",
      "complete -c 'pkg' -n '__pkg_is 0 n' -a 'help' -d 'Print this message or the help of the given subcommand(s)'",
      "complete -c 'pkg' -n '__pkg_is 1 n v' -s 'D' -l 'dev' -d 'Add as development dependencies'",
      "complete -c 'pkg' -n '__pkg_is 1 n v' -l 'registry' -x -d 'Registry to fetch from'",
      "complete -c 'pkg' -n '__pkg_is 1 n v' -l 'color' -x -a '(__pkg_values 1)' -d 'When to use color'",
      "complete -c 'pkg' -n '__pkg_is 1 n v' -s 'v' -l 'verbose' -d 'More output; repeat for more'",
      "complete -c 'pkg' -n '__pkg_is 1 n v' -s 'C' -x -a '(__fish_complete_directories)' -d 'Run as if started in DIR'",
      "complete -c 'pkg' -n '__pkg_is 1 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'pkg' -n '__pkg_is 2 n v' -l 'color' -x -a '(__pkg_values 1)' -d 'When to use color'",
      "complete -c 'pkg' -n '__pkg_is 2 n v' -s 'v' -l 'verbose' -d 'More output; repeat for more'",
      "complete -c 'pkg' -n '__pkg_is 2 n v' -s 'C' -x -a '(__fish_complete_directories)' -d 'Run as if started in DIR'",
      "complete -c 'pkg' -n '__pkg_is 2 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'pkg' -n '__pkg_is 3 n v' -s 'a' -l 'all' -d 'Include transitive packages'",
      "complete -c 'pkg' -n '__pkg_is 3 n v' -l 'format' -x -a '(__pkg_values 2)' -d 'Output format'",
      "complete -c 'pkg' -n '__pkg_is 3 n v' -l 'color' -x -a '(__pkg_values 1)' -d 'When to use color'",
      "complete -c 'pkg' -n '__pkg_is 3 n v' -s 'v' -l 'verbose' -d 'More output; repeat for more'",
      "complete -c 'pkg' -n '__pkg_is 3 n v' -s 'C' -x -a '(__fish_complete_directories)' -d 'Run as if started in DIR'",
      "complete -c 'pkg' -n '__pkg_is 3 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'pkg' -n '__pkg_is 4 n v' -l 'color' -x -a '(__pkg_values 1)' -d 'When to use color'",
      "complete -c 'pkg' -n '__pkg_is 4 n v' -s 'v' -l 'verbose' -d 'More output; repeat for more'",
      "complete -c 'pkg' -n '__pkg_is 4 n v' -s 'C' -x -a '(__fish_complete_directories)' -d 'Run as if started in DIR'",
      "complete -c 'pkg' -n '__pkg_is 4 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'pkg' -n '__pkg_is 5 n v' -l 'color' -x -a '(__pkg_values 1)' -d 'When to use color'",
      "complete -c 'pkg' -n '__pkg_is 5 n v' -s 'v' -l 'verbose' -d 'More output; repeat for more'",
      "complete -c 'pkg' -n '__pkg_is 5 n v' -s 'C' -x -a '(__fish_complete_directories)' -d 'Run as if started in DIR'",
      "complete -c 'pkg' -n '__pkg_is 5 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'pkg' -n '__pkg_is 5 p1' -a '(__pkg_values 3)'",
    ],
  ]))

def quirks_fish() -> String:
  page(List.concat(&2, String, [
    [
      "# fish completion; needs fish 3.3 or later.",
      "",
      "# Prints the number of the path that subcommand $argv[2] of path $argv[1]",
      "# enters; paths are numbered in pre-order from 0, the root.",
      "function __my_tool_dest",
      "    switch \"$argv[1] $argv[2]\"",
      "        case '0 remote' '0 rem'",
      "            echo 1",
      "        case '1 add'",
      "            echo 2",
      "        case '*'",
      "            return 1",
      "    end",
      "end",
      "",
      "# Succeeds when option $argv[2] takes the next word as its value at path",
      "# $argv[1].",
      "function __my_tool_valued",
      "    switch $argv[1]",
      "        case 0",
      "            contains -- $argv[2] '-o' '--out' '--output'",
      "        case 2",
      "            contains -- $argv[2] '-t' '--tag'",
      "        case '*'",
      "            return 1",
      "    end",
      "end",
      "",
      "# Prints how path $argv[1] takes words: 1 if it has subcommands, else 0; the",
      "# slot of its variadic positional, or 0; 1 if that slot is rest(), else 0.",
      "function __my_tool_shape",
      "    switch $argv[1]",
      "        case 0",
      "            echo 1 0 0",
      "        case 1",
      "            echo 1 0 0",
      "        case '*'",
      "            echo 0 0 0",
      "    end",
      "end",
      "",
      "# Prints the values of the one_of list numbered $argv[1].",
      "function __my_tool_values",
      "    switch $argv[1]",
      "        case 1",
      "            printf '%s\\n' 'it\\'s' 'a b' '$x' 'c:d' 'e\\\\f'",
      "    end",
      "end",
    ],
    fish_is("__my_tool"),
    [
      "",
      "# Option lines also hold at v, so that fish can read grouped short options",
      "# before a value, as in -vC DIR.",
      "complete -c 'my-tool' -f",
      "complete -c 'my-tool' -n '__my_tool_is 0 n v' -s 'q' -l 'quiet' -l 'no-quiet' -d 'Say less'",
      "complete -c 'my-tool' -n '__my_tool_is 0 n v' -l 'mode' -a '(__my_tool_values 1)' -d 'Pick a mode: [a] or b'",
      "complete -c 'my-tool' -n '__my_tool_is 0 n v' -s 'o' -l 'out' -l 'output' -r -F -d 'Write to FILE'",
      "complete -c 'my-tool' -n '__my_tool_is 0 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'my-tool' -n '__my_tool_is 0 n' -s 'V' -l 'version' -d 'Print version'",
      "complete -c 'my-tool' -n '__my_tool_is 0 n h' -a 'remote' -d 'Manage remotes'",
      "complete -c 'my-tool' -n '__my_tool_is 0 n h' -a 'rem' -d 'Manage remotes'",
      "complete -c 'my-tool' -n '__my_tool_is 0 n' -a 'help' -d 'Print this message or the help of the given subcommand(s)'",
      "complete -c 'my-tool' -n '__my_tool_is 1 n v' -s 'q' -l 'quiet' -l 'no-quiet' -d 'Say less'",
      "complete -c 'my-tool' -n '__my_tool_is 1 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'my-tool' -n '__my_tool_is 1 n h' -a 'add' -d 'Add a remote'",
      "complete -c 'my-tool' -n '__my_tool_is 1 n' -a 'help' -d 'Print this message or the help of the given subcommand(s)'",
      "complete -c 'my-tool' -n '__my_tool_is 2 n v' -s 't' -l 'tag' -x -d 'Tag the remote'",
      "complete -c 'my-tool' -n '__my_tool_is 2 n v' -s 'q' -l 'quiet' -l 'no-quiet' -d 'Say less'",
      "complete -c 'my-tool' -n '__my_tool_is 2 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'my-tool' -n '__my_tool_is 2 p2' -a '(__fish_complete_directories)'",
    ],
  ]))

def launch_fish() -> String:
  page(List.concat(&2, String, [
    [
      "# fish completion; needs fish 3.3 or later.",
      "",
      "# Prints the number of the path that subcommand $argv[2] of path $argv[1]",
      "# enters; paths are numbered in pre-order from 0, the root.",
      "function __launch_dest",
      "    switch \"$argv[1] $argv[2]\"",
      "        case '*'",
      "            return 1",
      "    end",
      "end",
      "",
      "# Succeeds when option $argv[2] takes the next word as its value at path",
      "# $argv[1].",
      "function __launch_valued",
      "    switch $argv[1]",
      "        case '*'",
      "            return 1",
      "    end",
      "end",
      "",
      "# Prints how path $argv[1] takes words: 1 if it has subcommands, else 0; the",
      "# slot of its variadic positional, or 0; 1 if that slot is rest(), else 0.",
      "function __launch_shape",
      "    switch $argv[1]",
      "        case 0",
      "            echo 0 2 1",
      "        case '*'",
      "            echo 0 0 0",
      "    end",
      "end",
    ],
    fish_is("__launch"),
    [
      "",
      "# Option lines also hold at v, so that fish can read grouped short options",
      "# before a value, as in -vC DIR.",
      "complete -c 'launch' -f",
      "complete -c 'launch' -n '__launch_is 0 n v' -s 'n' -l 'dry-run' -d 'Print the command instead'",
      "complete -c 'launch' -n '__launch_is 0 n h' -s 'h' -l 'help' -d 'Print help'",
      "complete -c 'launch' -n '__launch_is 0 p1' -F",
      "complete -c 'launch' -n '__launch_is 0 p2' -F",
    ],
  ]))

def pkg_zsh() -> String:
  page([
    "#compdef pkg",
    "",
    "_pkg() {",
    "  local curcontext=$curcontext state line",
    "  local -a v1=('auto' 'always' 'never') v2=('text' 'json') v3=('bash' 'zsh' 'fish')",
    "  # _arguments -S drops a -- typed before a command's first word, so a",
    "  # state whose words hold fewer -- than the line has is past one.",
    "  local -i ends=${#${(M)words[2,CURRENT-1]:#--}}",
    "  _arguments -C -s -S \\",
    "    '--color=[When to use color]:WHEN:($v1)' \\",
    "    '*-v[More output; repeat for more]' \\",
    "    '*--verbose[More output; repeat for more]' \\",
    "    '-C+[Run as if started in DIR]:DIR:_files -/' \\",
    "    '(-h --help)-h[Print help]' \\",
    "    '(-h --help)--help[Print help]' \\",
    "    '(-V --version)-V[Print version]' \\",
    "    '(-V --version)--version[Print version]' \\",
    "    '*:: :->pkg' && return",
    "  case $state in",
    "    'pkg')",
    "      (( ${#${(M)words[1,CURRENT-1]:#--}} < ends )) && return 1",
    "      if (( CURRENT == 1 )); then",
    "        local -a commands=(",
    "          'add:Add packages'",
    "          'remove:Remove packages'",
    "          'rm:Remove packages'",
    "          'list:List installed packages'",
    "          'run:Run a package script'",
    "          'completions:Print a shell completion script'",
    "          'help:Print this message or the help of the given subcommand(s)'",
    "        )",
    "        _describe -t commands 'pkg command' commands",
    "      else",
    "        case $words[1] in",
    "          'add')",
    "            _arguments -C -s -S \\",
    "              '(-D --dev)-D[Add as development dependencies]' \\",
    "              '(-D --dev)--dev[Add as development dependencies]' \\",
    "              '--registry=[Registry to fetch from]:URL: ' \\",
    "              '--color=[When to use color]:WHEN:($v1)' \\",
    "              '*-v[More output; repeat for more]' \\",
    "              '*--verbose[More output; repeat for more]' \\",
    "              '-C+[Run as if started in DIR]:DIR:_files -/' \\",
    "              '(-h --help)-h[Print help]' \\",
    "              '(-h --help)--help[Print help]' \\",
    "              '*:NAME: ' ;;",
    "          'remove'|'rm')",
    "            _arguments -C -s -S \\",
    "              '--color=[When to use color]:WHEN:($v1)' \\",
    "              '*-v[More output; repeat for more]' \\",
    "              '*--verbose[More output; repeat for more]' \\",
    "              '-C+[Run as if started in DIR]:DIR:_files -/' \\",
    "              '(-h --help)-h[Print help]' \\",
    "              '(-h --help)--help[Print help]' \\",
    "              '*:NAME: ' ;;",
    "          'list')",
    "            _arguments -C -s -S \\",
    "              '(-a --all)-a[Include transitive packages]' \\",
    "              '(-a --all)--all[Include transitive packages]' \\",
    "              '--format=[Output format]:FMT:($v2)' \\",
    "              '--color=[When to use color]:WHEN:($v1)' \\",
    "              '*-v[More output; repeat for more]' \\",
    "              '*--verbose[More output; repeat for more]' \\",
    "              '-C+[Run as if started in DIR]:DIR:_files -/' \\",
    "              '(-h --help)-h[Print help]' \\",
    "              '(-h --help)--help[Print help]' ;;",
    "          'run')",
    "            _arguments -C -s -S \\",
    "              '--color=[When to use color]:WHEN:($v1)' \\",
    "              '*-v[More output; repeat for more]' \\",
    "              '*--verbose[More output; repeat for more]' \\",
    "              '-C+[Run as if started in DIR]:DIR:_files -/' \\",
    "              '(-h --help)-h[Print help]' \\",
    "              '(-h --help)--help[Print help]' \\",
    "              '1:SCRIPT: ' \\",
    "              '(-)2::ARGS: ' ;;",
    "          'completions')",
    "            _arguments -C -s -S \\",
    "              '--color=[When to use color]:WHEN:($v1)' \\",
    "              '*-v[More output; repeat for more]' \\",
    "              '*--verbose[More output; repeat for more]' \\",
    "              '-C+[Run as if started in DIR]:DIR:_files -/' \\",
    "              '(-h --help)-h[Print help]' \\",
    "              '(-h --help)--help[Print help]' \\",
    "              '1:SHELL:($v3)' ;;",
    "          'help')",
    "            _arguments -C -s -S \\",
    "              '(-h --help)-h[Print help]' \\",
    "              '(-h --help)--help[Print help]' \\",
    "              '*:: :->pkg-help' && return",
    "            case $state in",
    "              'pkg-help')",
    "                (( ${#${(M)words[1,CURRENT-1]:#--}} < ends )) && return 1",
    "                if (( CURRENT == 1 )); then",
    "                  local -a commands=(",
    "                    'add:Add packages'",
    "                    'remove:Remove packages'",
    "                    'rm:Remove packages'",
    "                    'list:List installed packages'",
    "                    'run:Run a package script'",
    "                    'completions:Print a shell completion script'",
    "                  )",
    "                  _describe -t commands 'pkg command' commands",
    "                fi ;;",
    "            esac ;;",
    "        esac",
    "      fi ;;",
    "  esac",
    "}",
    "",
    "if [[ $funcstack[1] == '_pkg' ]]; then",
    "  _pkg \"$@\"",
    "else",
    "  compdef _pkg 'pkg'",
    "fi",
  ])

def quirks_zsh() -> String:
  page([
    "#compdef my-tool",
    "",
    "_my_tool() {",
    "  local curcontext=$curcontext state line",
    "  local -a v1=('it'\\''s' 'a b' '$x' 'c:d' 'e\\f')",
    "  # _arguments -S drops a -- typed before a command's first word, so a",
    "  # state whose words hold fewer -- than the line has is past one.",
    "  local -i ends=${#${(M)words[2,CURRENT-1]:#--}}",
    "  _arguments -C -s -S \\",
    "    '(-q --quiet --no-quiet)-q[Say less]' \\",
    "    '(-q --quiet --no-quiet)--quiet[Say less]' \\",
    "    '(-q --quiet --no-quiet)--no-quiet[Say less]' \\",
    "    '--mode=-[Pick a mode\\: \\[a\\] or b]::M:($v1)' \\",
    "    '(-o --out --output)-o+[Write to FILE]:FILE:_files' \\",
    "    '(-o --out --output)--out=[Write to FILE]:FILE:_files' \\",
    "    '(-o --out --output)--output=[Write to FILE]:FILE:_files' \\",
    "    '(-h --help)-h[Print help]' \\",
    "    '(-h --help)--help[Print help]' \\",
    "    '(-V --version)-V[Print version]' \\",
    "    '(-V --version)--version[Print version]' \\",
    "    '*:: :->my-tool' && return",
    "  case $state in",
    "    'my-tool')",
    "      (( ${#${(M)words[1,CURRENT-1]:#--}} < ends )) && return 1",
    "      if (( CURRENT == 1 )); then",
    "        local -a commands=(",
    "          'remote:Manage remotes'",
    "          'rem:Manage remotes'",
    "          'help:Print this message or the help of the given subcommand(s)'",
    "        )",
    "        _describe -t commands 'my-tool command' commands",
    "      else",
    "        case $words[1] in",
    "          'remote'|'rem')",
    "            _arguments -C -s -S \\",
    "              '(-q --quiet --no-quiet)-q[Say less]' \\",
    "              '(-q --quiet --no-quiet)--quiet[Say less]' \\",
    "              '(-q --quiet --no-quiet)--no-quiet[Say less]' \\",
    "              '(-h --help)-h[Print help]' \\",
    "              '(-h --help)--help[Print help]' \\",
    "              '*:: :->my-tool-remote' && return",
    "            case $state in",
    "              'my-tool-remote')",
    "                (( ${#${(M)words[1,CURRENT-1]:#--}} < ends )) && return 1",
    "                if (( CURRENT == 1 )); then",
    "                  local -a commands=(",
    "                    'add:Add a remote'",
    "                    'help:Print this message or the help of the given subcommand(s)'",
    "                  )",
    "                  _describe -t commands 'my-tool remote command' commands",
    "                else",
    "                  case $words[1] in",
    "                    'add')",
    "                      _arguments -C -s -S \\",
    "                        '*-t+[Tag the remote]:T: ' \\",
    "                        '*--tag=[Tag the remote]:T: ' \\",
    "                        '(-q --quiet --no-quiet)-q[Say less]' \\",
    "                        '(-q --quiet --no-quiet)--quiet[Say less]' \\",
    "                        '(-q --quiet --no-quiet)--no-quiet[Say less]' \\",
    "                        '(-h --help)-h[Print help]' \\",
    "                        '(-h --help)--help[Print help]' \\",
    "                        '1:NAME: ' \\",
    "                        '2::DIR:_files -/' ;;",
    "                    'help')",
    "                      _arguments -C -s -S \\",
    "                        '(-h --help)-h[Print help]' \\",
    "                        '(-h --help)--help[Print help]' \\",
    "                        '*:: :->my-tool-remote-help' && return",
    "                      case $state in",
    "                        'my-tool-remote-help')",
    "                          (( ${#${(M)words[1,CURRENT-1]:#--}} < ends )) && return 1",
    "                          if (( CURRENT == 1 )); then",
    "                            local -a commands=(",
    "                              'add:Add a remote'",
    "                            )",
    "                            _describe -t commands 'my-tool remote command' commands",
    "                          fi ;;",
    "                      esac ;;",
    "                  esac",
    "                fi ;;",
    "            esac ;;",
    "          'help')",
    "            _arguments -C -s -S \\",
    "              '(-h --help)-h[Print help]' \\",
    "              '(-h --help)--help[Print help]' \\",
    "              '*:: :->my-tool-help' && return",
    "            case $state in",
    "              'my-tool-help')",
    "                (( ${#${(M)words[1,CURRENT-1]:#--}} < ends )) && return 1",
    "                if (( CURRENT == 1 )); then",
    "                  local -a commands=(",
    "                    'remote:Manage remotes'",
    "                    'rem:Manage remotes'",
    "                  )",
    "                  _describe -t commands 'my-tool command' commands",
    "                else",
    "                  case $words[1] in",
    "                    'remote'|'rem')",
    "                      if (( CURRENT == 2 )); then",
    "                        local -a commands=(",
    "                          'add:Add a remote'",
    "                        )",
    "                        _describe -t commands 'my-tool remote command' commands",
    "                      fi ;;",
    "                  esac",
    "                fi ;;",
    "            esac ;;",
    "        esac",
    "      fi ;;",
    "  esac",
    "}",
    "",
    "if [[ $funcstack[1] == '_my-tool' ]]; then",
    "  _my_tool \"$@\"",
    "else",
    "  compdef _my_tool 'my-tool'",
    "fi",
  ])

def launch_zsh() -> String:
  page([
    "#compdef launch",
    "",
    "_launch() {",
    "  local curcontext=$curcontext state line",
    "  _arguments -C -s -S \\",
    "    '(-n --dry-run)-n[Print the command instead]' \\",
    "    '(-n --dry-run)--dry-run[Print the command instead]' \\",
    "    '(-h --help)-h[Print help]' \\",
    "    '(-h --help)--help[Print help]' \\",
    "    '1:PROG:_files' \\",
    "    '(-)2::ARGS:_files'",
    "}",
    "",
    "if [[ $funcstack[1] == '_launch' ]]; then",
    "  _launch \"$@\"",
    "else",
    "  compdef _launch 'launch'",
    "fi",
  ])

def pkg_man() -> String:
  page([
    ".TH \"PKG\" \"1\" \"\" \"pkg 0.1.0\" \"User Commands\"",
    ".SH NAME",
    "pkg \\- A package manager (demo)",
    ".SH SYNOPSIS",
    "\\fBpkg\\fR [OPTIONS] <COMMAND>",
    ".SH DESCRIPTION",
    "A package manager (demo)",
    ".SH OPTIONS",
    ".TP",
    "\\fB\\-\\-color\\fR \\fI<WHEN>\\fR",
    "When to use color [default: auto] [possible values: auto, always, never]",
    ".TP",
    "\\fB\\-v\\fR, \\fB\\-\\-verbose\\fR...",
    "More output; repeat for more",
    ".TP",
    "\\fB\\-C\\fR \\fI<DIR>\\fR",
    "Run as if started in DIR",
    ".TP",
    "\\fB\\-h\\fR, \\fB\\-\\-help\\fR",
    "Print help",
    ".TP",
    "\\fB\\-V\\fR, \\fB\\-\\-version\\fR",
    "Print version",
    ".SH COMMANDS",
    ".TP",
    "\\fBpkg\\-add\\fR(1)",
    "Add packages",
    ".TP",
    "\\fBpkg\\-remove\\fR(1)",
    "Remove packages [aliases: rm]",
    ".TP",
    "\\fBpkg\\-list\\fR(1)",
    "List installed packages",
    ".TP",
    "\\fBpkg\\-run\\fR(1)",
    "Run a package script",
    ".TP",
    "\\fBpkg\\-completions\\fR(1)",
    "Print a shell completion script",
    ".SH EXIT STATUS",
    ".TP",
    "\\fB0\\fR",
    "Success",
    ".TP",
    "\\fB1\\fR",
    "Failure",
    ".TP",
    "\\fB2\\fR",
    "Usage error",
    ".TP",
    "\\fB70\\fR",
    "Internal software error",
    ".SH SEE ALSO",
    "\\fBpkg\\-add\\fR(1), \\fBpkg\\-remove\\fR(1), \\fBpkg\\-list\\fR(1), \\fBpkg\\-run\\fR(1), \\fBpkg\\-completions\\fR(1)",
  ])

def add_man() -> String:
  page([
    ".TH \"PKG\\-ADD\" \"1\" \"\" \"pkg 0.1.0\" \"User Commands\"",
    ".SH NAME",
    "pkg\\-add \\- Add packages",
    ".SH SYNOPSIS",
    "\\fBpkg add\\fR [OPTIONS] <NAME>...",
    ".SH DESCRIPTION",
    "Add packages",
    ".SH ARGUMENTS",
    ".TP",
    "\\fI<NAME>\\fR...",
    "Packages to add",
    ".SH OPTIONS",
    ".TP",
    "\\fB\\-D\\fR, \\fB\\-\\-dev\\fR",
    "Add as development dependencies",
    ".TP",
    "\\fB\\-\\-registry\\fR \\fI<URL>\\fR",
    "Registry to fetch from [env: PKG_REGISTRY] [default: https://registry.example]",
    ".TP",
    "\\fB\\-\\-color\\fR \\fI<WHEN>\\fR",
    "When to use color [default: auto] [possible values: auto, always, never]",
    ".TP",
    "\\fB\\-v\\fR, \\fB\\-\\-verbose\\fR...",
    "More output; repeat for more",
    ".TP",
    "\\fB\\-C\\fR \\fI<DIR>\\fR",
    "Run as if started in DIR",
    ".TP",
    "\\fB\\-h\\fR, \\fB\\-\\-help\\fR",
    "Print help",
    ".SH ENVIRONMENT",
    ".TP",
    "\\fBPKG_REGISTRY\\fR",
    "Used for \\fB\\-\\-registry\\fR \\fI<URL>\\fR when it is not given",
    ".SH EXIT STATUS",
    ".TP",
    "\\fB0\\fR",
    "Success",
    ".TP",
    "\\fB1\\fR",
    "Failure",
    ".TP",
    "\\fB2\\fR",
    "Usage error",
    ".TP",
    "\\fB70\\fR",
    "Internal software error",
    ".SH EXAMPLES",
    "Add a development dependency:",
    ".IP",
    ".nf",
    "$ pkg add \\-D left\\-pad",
    ".fi",
    ".SH SEE ALSO",
    "\\fBpkg\\fR(1)",
  ])

def quirks_man() -> String:
  page([
    ".TH \"MY\\-TOOL\" \"1\" \"\" \"my\\-tool 2.0\\-rc.1\" \"User Commands\"",
    ".SH NAME",
    "my\\-tool \\- It\\(aqs a \\(dqtool\\(dq: [all] of it",
    ".SH SYNOPSIS",
    "\\fBmy\\-tool\\fR [OPTIONS] <COMMAND>",
    ".SH DESCRIPTION",
    "It\\(aqs a \\(dqtool\\(dq: [all] of it",
    ".PP",
    "Second paragraph.",
    ".br",
    "\\&.A hard break",
    ".SH OPTIONS",
    ".TP",
    "\\fB\\-q\\fR, \\fB\\-\\-[no\\-]quiet\\fR",
    "Say less",
    ".IP",
    "\\(aqQuoted\\(aq second paragraph [env: MY_QUIET]",
    ".TP",
    "\\fB\\-\\-mode\\fR[=\\fI<M>\\fR]",
    "Pick a mode: [a] or b [possible values: it\\(aqs, a b, $x, c:d, e\\ef]",
    ".TP",
    "\\fB\\-h\\fR, \\fB\\-\\-help\\fR",
    "Print help",
    ".TP",
    "\\fB\\-V\\fR, \\fB\\-\\-version\\fR",
    "Print version",
    ".SS \"Output\"",
    ".TP",
    "\\fB\\-o\\fR, \\fB\\-\\-out\\fR \\fI<FILE>\\fR",
    "Write to FILE [aliases: \\-\\-output]",
    ".SH COMMANDS",
    ".TP",
    "\\fBmy\\-tool\\-remote\\fR(1)",
    "Manage remotes [aliases: rem]",
    ".SH ENVIRONMENT",
    ".TP",
    "\\fBMY_QUIET\\fR",
    "Used for \\fB\\-\\-[no\\-]quiet\\fR when it is not given",
    ".SH EXIT STATUS",
    ".TP",
    "\\fB0\\fR",
    "Success",
    ".TP",
    "\\fB1\\fR",
    "Failure",
    ".TP",
    "\\fB2\\fR",
    "Usage error",
    ".TP",
    "\\fB70\\fR",
    "Internal software error",
    ".SH EXAMPLES",
    "Quote a mode:",
    ".IP",
    ".nf",
    "$ my\\-tool \\-\\-mode=\\(aqit\\(aq\\e\\(aq\\(aqs\\(aq rem add x",
    ".fi",
    ".PP",
    "Be quiet:",
    ".IP",
    ".nf",
    "$ my\\-tool \\-q",
    ".fi",
    ".SH NOTES",
    "\\(aqQuoted\\(aq notes\\ewith a backslash",
    ".SH SEE ALSO",
    "\\fBmy\\-tool\\-remote\\fR(1)",
  ])

def quirks_add_man() -> String:
  page([
    ".TH \"MY\\-TOOL\\-REMOTE\\-ADD\" \"1\" \"\" \"my\\-tool 2.0\\-rc.1\" \"User Commands\"",
    ".SH NAME",
    "my\\-tool\\-remote\\-add \\- Add a remote",
    ".SH SYNOPSIS",
    "\\fBmy\\-tool remote add\\fR [OPTIONS] <NAME> [DIR]",
    ".SH DESCRIPTION",
    "Add a remote",
    ".SH ARGUMENTS",
    ".TP",
    "\\fI<NAME>\\fR",
    "Remote name",
    ".TP",
    "\\fI[DIR]\\fR",
    "Where to clone",
    ".SH OPTIONS",
    ".TP",
    "\\fB\\-t\\fR, \\fB\\-\\-tag\\fR \\fI<T>\\fR...",
    "Tag the remote",
    ".TP",
    "\\fB\\-q\\fR, \\fB\\-\\-[no\\-]quiet\\fR",
    "Say less",
    ".IP",
    "\\(aqQuoted\\(aq second paragraph [env: MY_QUIET]",
    ".TP",
    "\\fB\\-h\\fR, \\fB\\-\\-help\\fR",
    "Print help",
    ".SH ENVIRONMENT",
    ".TP",
    "\\fBMY_QUIET\\fR",
    "Used for \\fB\\-\\-[no\\-]quiet\\fR when it is not given",
    ".SH EXIT STATUS",
    ".TP",
    "\\fB0\\fR",
    "Success",
    ".TP",
    "\\fB1\\fR",
    "Failure",
    ".TP",
    "\\fB2\\fR",
    "Usage error",
    ".TP",
    "\\fB70\\fR",
    "Internal software error",
    ".SH SEE ALSO",
    "\\fBmy\\-tool\\-remote\\fR(1)",
  ])

def quirks_prune_man() -> String:
  page([
    ".TH \"MY\\-TOOL\\-REMOTE\\-PRUNE\" \"1\" \"\" \"my\\-tool 2.0\\-rc.1\" \"User Commands\"",
    ".SH NAME",
    "my\\-tool\\-remote\\-prune \\- Prune remotes",
    ".SH SYNOPSIS",
    "\\fBmy\\-tool remote prune\\fR [OPTIONS]",
    ".SH DESCRIPTION",
    "Prune remotes",
    ".SH OPTIONS",
    ".TP",
    "\\fB\\-q\\fR, \\fB\\-\\-[no\\-]quiet\\fR",
    "Say less",
    ".IP",
    "\\(aqQuoted\\(aq second paragraph [env: MY_QUIET]",
    ".TP",
    "\\fB\\-h\\fR, \\fB\\-\\-help\\fR",
    "Print help",
    ".SH ENVIRONMENT",
    ".TP",
    "\\fBMY_QUIET\\fR",
    "Used for \\fB\\-\\-[no\\-]quiet\\fR when it is not given",
    ".SH EXIT STATUS",
    ".TP",
    "\\fB0\\fR",
    "Success",
    ".TP",
    "\\fB1\\fR",
    "Failure",
    ".TP",
    "\\fB2\\fR",
    "Usage error",
    ".TP",
    "\\fB70\\fR",
    "Internal software error",
    ".SH SEE ALSO",
    "\\fBmy\\-tool\\-remote\\fR(1)",
  ])

def launch_man() -> String:
  page([
    ".TH \"LAUNCH\" \"1\" \"\" \"launch\" \"User Commands\"",
    ".SH NAME",
    "launch \\- Start a program",
    ".SH SYNOPSIS",
    "\\fBlaunch\\fR [OPTIONS] <PROG> [ARGS]...",
    ".SH DESCRIPTION",
    "Start a program",
    ".SH ARGUMENTS",
    ".TP",
    "\\fI<PROG>\\fR",
    "Program to start",
    ".TP",
    "\\fI[ARGS]\\fR...",
    "Arguments for the program",
    ".SH OPTIONS",
    ".TP",
    "\\fB\\-n\\fR, \\fB\\-\\-dry\\-run\\fR",
    "Print the command instead",
    ".TP",
    "\\fB\\-h\\fR, \\fB\\-\\-help\\fR",
    "Print help",
    ".SH EXIT STATUS",
    ".TP",
    "\\fB0\\fR",
    "Success",
    ".TP",
    "\\fB1\\fR",
    "Failure",
    ".TP",
    "\\fB2\\fR",
    "Usage error",
    ".TP",
    "\\fB70\\fR",
    "Internal software error",
  ])

# G-COMP: pkg's scripts. Each path offers its visible subcommands with
# their aliases and help, the options in scope with -h and --help (and -V
# and --version at the root), one_of values and directories for -C. The
# hidden man command never appears.
law g_comp_bash:
  {Cli.script(Demo.cli(), Cli.Bash{}) == pkg_bash() : String}

law g_comp_zsh:
  {Cli.script(Demo.cli(), Cli.Zsh{}) == pkg_zsh() : String}

law g_comp_fish:
  {Cli.script(Demo.cli(), Cli.Fish{}) == pkg_fish() : String}

# §11: a spec whose text needs every quoter: quotes, $, \, [, ], : and a
# space in values and help, a leading dot, a dash in the name, hidden items,
# subcommand and option aliases, a [=<V>] option, a heading, a negatable
# switch with env, examples and after() text.
def quirks() -> Cli.Cmd:
  Cli.cmd("my-tool",
    "It's a \"tool\": [all] of it\n\nSecond paragraph.\n.A hard break", [
    Cli.version("2.0-rc.1"),
    Cli.arg("-q, --[no-]quiet", "Say less\n\n'Quoted' second paragraph",
      [Cli.global(), Cli.env("MY_QUIET")]),
    Cli.arg("--mode[=<M>]", "Pick a mode: [a] or b",
      [Cli.one_of(["it's", "a b", "$x", "c:d", "e\\f"]), Cli.bare("a b")]),
    Cli.arg("--key <K>", "Secret", [Cli.hidden()]),
    Cli.arg("-o, --out <FILE>", "Write to FILE",
      [Cli.as_file(), Cli.alias("--output"), Cli.heading("Output")]),
    Cli.sub("remote", "Manage remotes", [
      Cli.alias("rem"),
      Cli.sub("add", "Add a remote", [
        Cli.arg("-t, --tag <T>...", "Tag the remote", []),
        Cli.arg("<NAME>", "Remote name", []),
        Cli.arg("[DIR]", "Where to clone", [Cli.as_dir()]),
      ]),
      Cli.sub("prune", "Prune remotes", [Cli.hidden()]),
    ]),
    Cli.example("my-tool --mode='it'\\''s' rem add x", "Quote a mode"),
    Cli.example("my-tool -q", "Be quiet"),
    Cli.after("'Quoted' notes\\with a backslash"),
  ])

# G-COMP: the quirks scripts, for a spec that lints clean. Identifiers map
# - to _; words, descriptions and values pass through the quoters; --key
# and prune never appear; a [=<V>] option completes its value only after =.
law g_comp_quirks_bash:
  {Cli.problems(quirks()) == [] : List<&2, Cli.Problem>} &
  {Cli.script(quirks(), Cli.Bash{}) == quirks_bash() : String}

law g_comp_quirks_zsh:
  {Cli.script(quirks(), Cli.Zsh{}) == quirks_zsh() : String}

law g_comp_quirks_fish:
  {Cli.script(quirks(), Cli.Fish{}) == quirks_fish() : String}

# §11: a spec without a version, whose rest() slot takes files.
def launch() -> Cli.Cmd:
  Cli.cmd("launch", "Start a program", [
    Cli.arg("-n, --dry-run", "Print the command instead", []),
    Cli.arg("<PROG>", "Program to start", [Cli.as_file()]),
    Cli.arg("[ARGS]...", "Arguments for the program",
      [Cli.rest(), Cli.as_file()]),
  ])

# G-COMP: the launch scripts, for a spec that lints clean. The rest() slot
# completes files for its first value only, since that value takes every
# later word; without a version there is no -V.
law g_comp_launch_bash:
  {Cli.problems(launch()) == [] : List<&2, Cli.Problem>} &
  {Cli.script(launch(), Cli.Bash{}) == launch_bash() : String}

law g_comp_launch_zsh:
  {Cli.script(launch(), Cli.Zsh{}) == launch_zsh() : String}

law g_comp_launch_fish:
  {Cli.script(launch(), Cli.Fish{}) == launch_fish() : String}

# G-MAN: the pkg and pkg-add pages. The header has no date; COMMANDS lists
# each visible subcommand's page and summary, and SEE ALSO the parent's and
# subcommands' pages. help is not a page.
law g_man_pkg:
  {Cli.roff(Demo.cli(), []) == pkg_man() : String}

law g_man_add:
  {Cli.roff(Demo.cli(), ["add"]) == add_man() : String}

# G-MAN: roff renders the longest valid prefix of the path, through aliases
# and hidden commands, with the canonical names in the page name.
law g_man_path:
  {Cli.roff(Demo.cli(), ["rm"]) == Cli.roff(Demo.cli(), ["remove"])
    : String} &
  {Cli.roff(Demo.cli(), ["add", "x"]) == add_man() : String} &
  {Cli.roff(Demo.cli(), ["nope", "add"]) == pkg_man() : String} &
  {Cli.roff(Demo.cli(), ["help"]) == pkg_man() : String}

# G-MAN: the quirks pages. Paragraphs break with .PP, or .IP inside an
# entry; hard line breaks with .br. Tags end the last paragraph. A heading's
# options follow the built-ins under .SS; ENVIRONMENT names the arg each
# variable fills; after() text is NOTES. Hidden items have no entry, but a
# hidden command has a page.
law g_man_quirks:
  {Cli.roff(quirks(), []) == quirks_man() : String} &
  {Cli.roff(quirks(), ["rem", "add"]) == quirks_add_man() : String} &
  {Cli.roff(quirks(), ["remote", "prune"]) == quirks_prune_man() : String}

# G-MAN: a root without a version has its name alone in the header, and no
# -V in OPTIONS.
law g_man_launch:
  {Cli.roff(launch(), []) == launch_man() : String}

# G-MAN: an arg with several variables has one ENVIRONMENT entry naming them
# all, which says the first that is set wins.
law g_man_env_names:
  {Cli.roff(env_chain(), []) == page([
    ".TH \"TOOL\" \"1\" \"\" \"tool\" \"User Commands\"",
    ".SH NAME",
    "tool \\- Tool",
    ".SH SYNOPSIS",
    "\\fBtool\\fR [OPTIONS]",
    ".SH DESCRIPTION",
    "Tool",
    ".SH OPTIONS",
    ".TP",
    "\\fB\\-\\-out\\fR \\fI<X>\\fR",
    "Output [env: TOOL_OUT, LEGACY_OUT] [default: d]",
    ".TP",
    "\\fB\\-\\-n\\fR \\fI<N>\\fR",
    "Count [env: TOOL_N, LEGACY_N]",
    ".TP",
    "\\fB\\-h\\fR, \\fB\\-\\-help\\fR",
    "Print help",
    ".SH ENVIRONMENT",
    ".TP",
    "\\fBTOOL_OUT\\fR, \\fBLEGACY_OUT\\fR",
    "Used for \\fB\\-\\-out\\fR \\fI<X>\\fR when it is not given; the first that is set wins",
    ".TP",
    "\\fBTOOL_N\\fR, \\fBLEGACY_N\\fR",
    "Used for \\fB\\-\\-n\\fR \\fI<N>\\fR when it is not given; the first that is set wins",
    ".SH EXIT STATUS",
    ".TP",
    "\\fB0\\fR",
    "Success",
    ".TP",
    "\\fB1\\fR",
    "Failure",
    ".TP",
    "\\fB2\\fR",
    "Usage error",
    ".TP",
    "\\fB70\\fR",
    "Internal software error",
  ]) : String}

def pkg_run(h: Cli.Host, argv: List<&2, String>) -> Cli.Step<Demo.Action>:
  Cli.eval(~Demo.Action, ~Demo.decode, Demo.cli(), h, argv)

def shown(-A: Type, out: String) -> Cli.Step<A>:
  Cli.Quit{0, out, ""}

# V6: completions prints script(c, shell) and man prints roff(c, path) on
# stdout with exit 0, uncolored, before any decoder runs. Help and scan
# errors come first. A sub() named like a built-in is an ordinary command.
law g_eval_builtins:
  {pkg_run(host(), ["completions", "bash"]) ==
    shown(Demo.Action, pkg_bash()) : Cli.Step<Demo.Action>} &
  {pkg_run(host(), ["completions", "zsh"]) ==
    shown(Demo.Action, pkg_zsh()) : Cli.Step<Demo.Action>} &
  {pkg_run(tty(), ["--color=always", "completions", "fish"]) ==
    shown(Demo.Action, pkg_fish()) : Cli.Step<Demo.Action>} &
  {Cli.eval(~Bool, ~(+m => Cli.bug(Bool, "b")), Demo.cli(), host(),
    ["completions", "bash"]) == shown(Bool, pkg_bash()) : Cli.Step<Bool>} &
  {Cli.eval(~Bool, ~(+m => Cli.bug(Bool, "b")), Demo.cli(), host(),
    ["man", "add"]) == shown(Bool, add_man()) : Cli.Step<Bool>} &
  {pkg_run(host(), ["man"]) == shown(Demo.Action, pkg_man())
    : Cli.Step<Demo.Action>} &
  {pkg_run(tty(), ["-v", "man", "add"]) == shown(Demo.Action, add_man())
    : Cli.Step<Demo.Action>} &
  {pkg_run(host(), ["man", "rm"]) ==
    shown(Demo.Action, Cli.roff(Demo.cli(), ["remove"]))
    : Cli.Step<Demo.Action>} &
  {pkg_run(host(), ["man", "nope"]) == shown(Demo.Action, pkg_man())
    : Cli.Step<Demo.Action>} &
  {pkg_run(host(), ["completions", "bash", "--help"]) ==
    shown(Demo.Action, Cli.help(Demo.cli(), ["completions"], True{}, host()))
    : Cli.Step<Demo.Action>} &
  {pkg_run(host(), ["completions"]) == failed(Demo.Action,
    "the following required arguments were not provided:\n  <SHELL>", [],
    "pkg completions [OPTIONS] <SHELL>") : Cli.Step<Demo.Action>} &
  {pkg_run(host(), ["completions", "pwsh"]) == failed(Demo.Action,
    "invalid value 'pwsh' for '<SHELL>': expected one of 'bash', 'zsh', 'fish'",
    [], "pkg completions [OPTIONS] <SHELL>") : Cli.Step<Demo.Action>} &
  {ran(lookalikes(), host(), ["man"]) == went_to(["man"], [], None{})
    : Cli.Step<Parsed>}
