# Purpose: laws for the pure CLI library and pkg demo.
# Expected output: ALL PROOFS CHECK.
# Run: bend PROOF.bend --verdict
# Scope: P13 bounds visible line widths; it does not prove word preservation
# or whitespace normalization. G-TEXT pins representative wrapped content.

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
law p13:
  for s: String
  for +cols: Nat
  {List.all(~&2, ~String, ~(+line => Bool.or(
    Nat.is_le(Cli.width(Cli.strip(line)), cols),
    Nat.is_le(List.length(&2, String,
      List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
        String.split(line, ' '))), 1n))),
    String.lines(Cli.wrap(s, cols))) == True{} : Bool}

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
