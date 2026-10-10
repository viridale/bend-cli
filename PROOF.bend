# Purpose: proofs of the pure CLI laws.
# Expected output: ALL PROOFS CHECK.
# Run: bend PROOF.bend --verdict

import Base
import ./cli.bend as Cli
import ./LAWS.bend as Laws

def Laws.g_text_width():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.g_text_wrap():
  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))

def Laws.g_text_paint():
  ({==}, {==})

def Laws.g_text_strip():
  {==}

def Laws.g_text_emit():
  ({==}, {==})

def Laws.g_usage_forms():
  ({==}, {==})

def Laws.g_lint_valid():
  {==}

def Laws.g_lint_bad_usage():
  {==}

def Laws.g_lint_bad_usage_trailing_dot():
  ({==}, {==})

def Laws.g_lint_bad_name():
  {==}

def Laws.g_lint_dup():
  {==}

def Laws.g_lint_dup_repeat():
  {==}

def Laws.g_lint_dup_id():
  {==}

def Laws.g_lint_dup_sub():
  {==}

def Laws.g_lint_reserved():
  {==}

def Laws.g_lint_reserved_sub():
  {==}

def Laws.g_lint_misplaced():
  {==}

def Laws.g_lint_no_help():
  {==}

def Laws.g_lint_no_help_sub():
  {==}

def Laws.g_lint_bad_default():
  {==}

def Laws.g_lint_bad_ref():
  {==}

def Laws.g_lint_bad_positional():
  {==}

def Laws.g_lint_bad_positional_two_variadics():
  {==}

def Laws.g_lint_bad_positional_optional_after_variadic():
  {==}

def Laws.g_lint_bad_positional_rest():
  {==}

def Laws.g_lint_mixed():
  {==}

def Laws.g_lint_bad_choices():
  {==}

def Laws.g_lint_need_bare():
  {==}

def EscFree(s: String) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{head, tail}:
      {Char.is_eq(head, '\u{1B}') == False{} : Bool} & EscFree(tail)

def starts_empty(s: String) ->
    {String.starts_with(s, "") == True{} : Bool}:
  match s:
    case SNil{}: {==}
    case SCon{head, tail}: {==}

def starts_if_identity(t: String, b: Bool) ->
    {String.starts_with.if(t, "", b) == b : Bool}:
  match b:
    case False{}: {==}
    case True{}: starts_empty(t)

def starts_one(h: Char, t: String) ->
    {String.starts_with(SCon{h, t}, "\u{1B}")
      == Char.is_eq(h, '\u{1B}') : Bool}:
  starts_if_identity(t, Char.is_eq(h, '\u{1B}'))

def contains_if_or(t: String, b: Bool) ->
    {String.contains.if(t, "\u{1B}", b)
      == Bool.or(b, String.contains(t, "\u{1B}")) : Bool}:
  match b:
    case False{}: {==}
    case True{}: {==}

def contains_step(+h: Char, +t: String) ->
    {String.contains(SCon{h, t}, "\u{1B}")
      == Bool.or(Char.is_eq(h, '\u{1B}'),
        String.contains(t, "\u{1B}")) : Bool}:
  Equal.trans(Bool,
    String.contains(SCon{h, t}, "\u{1B}"),
    String.contains.if(t, "\u{1B}", Char.is_eq(h, '\u{1B}')),
    Bool.or(Char.is_eq(h, '\u{1B}'), String.contains(t, "\u{1B}")),
    Equal.cong(Bool, Bool,
      b => String.contains.if(t, "\u{1B}", b),
      String.starts_with(SCon{h, t}, "\u{1B}"),
      Char.is_eq(h, '\u{1B}'), starts_one(h, t)),
    contains_if_or(t, Char.is_eq(h, '\u{1B}')))

def bool_disc(b: Bool) -> Data:
  match b:
    case True{}: Unit
    case False{}: Empty

def true_false_absurd(e: {True{} == False{} : Bool}) -> Empty:
  %e : bool_disc(_)
  Unit{}

def or_false_parts(b: Bool, c: Bool,
    e: {Bool.or(b, c) == False{} : Bool}) ->
    ({b == False{} : Bool} & {c == False{} : Bool}):
  match b c:
    case True{} _:
      Empty.absurd({True{} == False{} : Bool} &
        {c == False{} : Bool}, true_false_absurd(e))
    case False{} True{}:
      Empty.absurd({False{} == False{} : Bool} &
        {True{} == False{} : Bool}, true_false_absurd(e))
    case False{} False{}:
      ({==}, {==})

def contains_false_parts(+h: Char, +t: String,
    prem: {String.contains(SCon{h, t}, "\u{1B}") == False{} : Bool}) ->
    ({Char.is_eq(h, '\u{1B}') == False{} : Bool} &
      {String.contains(t, "\u{1B}") == False{} : Bool}):
  or_false_parts(Char.is_eq(h, '\u{1B}'),
    String.contains(t, "\u{1B}"),
    Equal.trans(Bool,
      Bool.or(Char.is_eq(h, '\u{1B}'), String.contains(t, "\u{1B}")),
      String.contains(SCon{h, t}, "\u{1B}"), False{},
      Equal.sym(Bool, String.contains(SCon{h, t}, "\u{1B}"),
        Bool.or(Char.is_eq(h, '\u{1B}'), String.contains(t, "\u{1B}")),
        contains_step(h, t)), prem))

def pair_elim(-A: Type, -B: Type, -C: Type,
    p: A & B, f: A -> B -> C) -> C:
  (a, b) = p
  f(a)(b)

def free_of_contains(s: String,
    prem: {String.contains(s, "\u{1B}") == False{} : Bool}) ->
    EscFree(s):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+head, +tail}:
      pair_elim(
        {Char.is_eq(head, '\u{1B}') == False{} : Bool},
        {String.contains(tail, "\u{1B}") == False{} : Bool},
        EscFree(SCon{head, tail}),
        contains_false_parts(head, tail, prem),
        head_free => tail_prem =>
          (head_free, free_of_contains(tail, tail_prem)))

def free_append_left(a: String, b: String,
    free: EscFree(String.append(a, b))) -> EscFree(a):
  match a:
    case SNil{}:
      Unit{}
    case SCon{head, tail}:
      (head_free, rest_free) = free
      (head_free, free_append_left(tail, b, rest_free))

def free_append_right(a: String, b: String,
    free: EscFree(String.append(a, b))) -> EscFree(b):
  match a:
    case SNil{}:
      free
    case SCon{head, tail}:
      (head_free, rest_free) = free
      free_append_right(tail, b, rest_free)

def free_append_parts(a: String, b: String,
    free: EscFree(String.append(a, b))) ->
    (EscFree(a) & EscFree(b)):
  match a:
    case SNil{}:
      (Unit{}, free)
    case SCon{+head, +tail}:
      (head_free, rest_free) = free
      pair_elim(EscFree(tail), EscFree(b),
        EscFree(SCon{head, tail}) & EscFree(b),
        free_append_parts(tail, b, rest_free),
        left_free => right_free =>
          ((head_free, left_free), right_free))

def append_char_cons(out: String, h: Char, tail: String) ->
    {String.append(String.append(out, Char.show(h)), tail)
      == String.append(out, SCon{h, tail}) : String}:
  match out:
    case SNil{}:
      {==}
    case SCon{head, rest}:
      %append_char_cons(rest, h, tail) :
        {SCon{head, String.append(String.append(rest, Char.show(h)), tail)}
          == SCon{head, _} : String}
      {==}

def append_nil(s: String) -> {String.append(s, "") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{head, tail}:
      %append_nil(tail) : {SCon{head, String.append(tail, "")}
        == SCon{head, _} : String}
      {==}

def append_assoc(a: String, b: String, c: String) ->
    {String.append(String.append(a, b), c)
      == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{head, tail}:
      %append_assoc(tail, b, c) :
        {SCon{head, String.append(String.append(tail, b), c)}
          == SCon{head, _} : String}
      {==}

def paint_append_shape(+codes: String, +text: String, +suffix: String) ->
    {String.append(String.append("\u{1B}[",
        String.append(codes,
          String.append("m", String.append(text, "\u{1B}[0m")))), suffix)
      == String.append("\u{1B}[",
        String.append(codes,
          String.append("m",
            String.append(text, String.append("\u{1B}[0m", suffix)))))
      : String}:
  %append_assoc(text, "\u{1B}[0m", suffix) :
    {String.append(String.append("\u{1B}[",
        String.append(codes,
          String.append("m", String.append(text, "\u{1B}[0m")))), suffix)
      == String.append("\u{1B}[",
        String.append(codes, String.append("m", _))) : String}
  %append_assoc("m", String.append(text, "\u{1B}[0m"), suffix) :
    {String.append(String.append("\u{1B}[",
        String.append(codes,
          String.append("m", String.append(text, "\u{1B}[0m")))), suffix)
      == String.append("\u{1B}[",
        String.append(codes, _)) : String}
  %append_assoc(codes,
      String.append("m", String.append(text, "\u{1B}[0m")), suffix) :
    {String.append(String.append("\u{1B}[",
        String.append(codes,
          String.append("m", String.append(text, "\u{1B}[0m")))), suffix)
      == String.append("\u{1B}[", _) : String}
  {==}

def strip_reset_free(s: String, +out: String, free: EscFree(s)) ->
    {Cli.strip_fuel(Nat.add(1n, String.length(String.append(s, "\u{1B}[0m"))),
      Cli.StripPlain{out}, String.append(s, "\u{1B}[0m"))
      == String.append(out, s) : String}:
  match s:
    case SNil{}:
      Equal.sym(String, String.append(out, ""), out, append_nil(out))
    case SCon{+head, +tail}:
      (not_esc, free_tail) = free
      +rest = String.append(tail, "\u{1B}[0m")
      +next_out = String.append(out, Char.show(head))
      step = Equal.cong(Bool, String,
        b => Cli.strip_fuel(Nat.add(1n, String.length(rest)),
          Bool.pick(Cli.StripState, b, Cli.StripEsc{out},
            Cli.StripPlain{next_out}), rest),
        Char.is_eq(head, '\u{1B}'), False{}, not_esc)
      Equal.trans(String,
        Cli.strip_fuel(Nat.add(1n, String.length(rest)),
          Bool.pick(Cli.StripState, Char.is_eq(head, '\u{1B}'),
            Cli.StripEsc{out}, Cli.StripPlain{next_out}), rest),
        Cli.strip_fuel(Nat.add(1n, String.length(rest)),
          Cli.StripPlain{next_out}, rest),
        String.append(out, SCon{head, tail}), step,
        Equal.trans(String,
          Cli.strip_fuel(Nat.add(1n, String.length(rest)),
            Cli.StripPlain{next_out}, rest),
          String.append(next_out, tail),
          String.append(out, SCon{head, tail}),
          strip_reset_free(tail, next_out, free_tail),
          append_char_cons(out, head, tail)))

def plain_skip_free(s: String, +suffix: String, +out: String,
    free: EscFree(s)) ->
    {Cli.strip_fuel(Nat.add(1n,
        String.length(String.append(s, suffix))), Cli.StripPlain{out},
      String.append(s, suffix))
      == Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
        Cli.StripPlain{String.append(out, s)}, suffix) : String}:
  match s:
    case SNil{}:
      Equal.cong(String, String,
        x => Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
          Cli.StripPlain{x}, suffix),
        out, String.append(out, ""),
        Equal.sym(String, String.append(out, ""), out, append_nil(out)))
    case SCon{+head, +tail}:
      (not_esc, free_tail) = free
      +rest = String.append(tail, suffix)
      +next_out = String.append(out, Char.show(head))
      step = Equal.cong(Bool, String,
        b => Cli.strip_fuel(Nat.add(1n, String.length(rest)),
          Bool.pick(Cli.StripState, b, Cli.StripEsc{out},
            Cli.StripPlain{next_out}), rest),
        Char.is_eq(head, '\u{1B}'), False{}, not_esc)
      Equal.trans(String,
        Cli.strip_fuel(Nat.add(1n, String.length(rest)),
          Bool.pick(Cli.StripState, Char.is_eq(head, '\u{1B}'),
            Cli.StripEsc{out}, Cli.StripPlain{next_out}), rest),
        Cli.strip_fuel(Nat.add(1n, String.length(rest)),
          Cli.StripPlain{next_out}, rest),
        Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
          Cli.StripPlain{String.append(out, SCon{head, tail})}, suffix),
        step,
        Equal.trans(String,
          Cli.strip_fuel(Nat.add(1n, String.length(rest)),
            Cli.StripPlain{next_out}, rest),
          Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
            Cli.StripPlain{String.append(next_out, tail)}, suffix),
          Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
            Cli.StripPlain{String.append(out, SCon{head, tail})}, suffix),
          plain_skip_free(tail, suffix, next_out, free_tail),
          Equal.cong(String, String,
            x => Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
              Cli.StripPlain{x}, suffix),
            String.append(next_out, tail),
            String.append(out, SCon{head, tail}),
            append_char_cons(out, head, tail))))

def reset_skip(suffix: String, out: String) ->
    {Cli.strip_fuel(Nat.add(1n,
        String.length(String.append("\u{1B}[0m", suffix))),
      Cli.StripPlain{out}, String.append("\u{1B}[0m", suffix))
      == Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
        Cli.StripPlain{out}, suffix) : String}:
  {==}

def scan_string_cong(a: String, b: String, state: Cli.StripState,
    e: {a == b : String}) ->
    {Cli.strip_fuel(Nat.add(1n, String.length(a)), state, a)
      == Cli.strip_fuel(Nat.add(1n, String.length(b)), state, b)
      : String}:
  Equal.cong(String, String,
    x => Cli.strip_fuel(Nat.add(1n, String.length(x)), state, x),
    a, b, e)

def body_skip_tail(styles: List<&2, Cli.Style>, +suffix: String,
    +out: String, pending: String) ->
    {Cli.strip_fuel(Nat.add(1n, String.length(
        String.append(Cli.style_codes_tail(styles),
          String.append("m", suffix)))),
      Cli.StripBody{out, pending},
      String.append(Cli.style_codes_tail(styles),
        String.append("m", suffix)))
      == Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
        Cli.StripPlain{out}, suffix) : String}:
  match styles:
    case Nil{}:
      {==}
    case head <> tail:
      match head:
        case Cli.Bold{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(pending, ";"), "1"))
        case Cli.Dim{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(pending, ";"), "2"))
        case Cli.Under{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(pending, ";"), "4"))
        case Cli.Red{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(String.append(pending, ";"), "3"), "1"))
        case Cli.Green{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(String.append(pending, ";"), "3"), "2"))
        case Cli.Yellow{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(String.append(pending, ";"), "3"), "3"))
        case Cli.Blue{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(String.append(pending, ";"), "3"), "4"))
        case Cli.Magenta{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(String.append(pending, ";"), "3"), "5"))
        case Cli.Cyan{}:
          body_skip_tail(tail, suffix, out,
            String.append(String.append(String.append(pending, ";"), "3"), "6"))

def body_skip_first(style: Cli.Style, tail: List<&2, Cli.Style>,
    +suffix: String, +out: String, pending: String) ->
    {Cli.strip_fuel(Nat.add(1n, String.length(
        String.append(String.append(Cli.style_code(style),
          Cli.style_codes_tail(tail)), String.append("m", suffix)))),
      Cli.StripBody{out, pending},
      String.append(String.append(Cli.style_code(style),
        Cli.style_codes_tail(tail)), String.append("m", suffix)))
      == Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
        Cli.StripPlain{out}, suffix) : String}:
  match style:
    case Cli.Bold{}:
      body_skip_tail(tail, suffix, out, String.append(pending, "1"))
    case Cli.Dim{}:
      body_skip_tail(tail, suffix, out, String.append(pending, "2"))
    case Cli.Under{}:
      body_skip_tail(tail, suffix, out, String.append(pending, "4"))
    case Cli.Red{}:
      body_skip_tail(tail, suffix, out,
        String.append(String.append(pending, "3"), "1"))
    case Cli.Green{}:
      body_skip_tail(tail, suffix, out,
        String.append(String.append(pending, "3"), "2"))
    case Cli.Yellow{}:
      body_skip_tail(tail, suffix, out,
        String.append(String.append(pending, "3"), "3"))
    case Cli.Blue{}:
      body_skip_tail(tail, suffix, out,
        String.append(String.append(pending, "3"), "4"))
    case Cli.Magenta{}:
      body_skip_tail(tail, suffix, out,
        String.append(String.append(pending, "3"), "5"))
    case Cli.Cyan{}:
      body_skip_tail(tail, suffix, out,
        String.append(String.append(pending, "3"), "6"))

def paint_skip_colored(+style: Cli.Style, +styles: List<&2, Cli.Style>,
    +source: String, +suffix: String, +out: String,
    free: EscFree(source)) ->
    {Cli.strip_fuel(Nat.add(1n, String.length(
        String.append(Cli.paint(True{}, style <> styles, source), suffix))),
      Cli.StripPlain{out},
      String.append(Cli.paint(True{}, style <> styles, source), suffix))
      == Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
        Cli.StripPlain{String.append(out, source)}, suffix) : String}:
  +codes = Cli.style_codes(style <> styles)
  +raw = String.append(Cli.paint(True{}, style <> styles, source), suffix)
  +after_reset = String.append("\u{1B}[0m", suffix)
  +after_text = String.append(source, after_reset)
  +shaped = String.append("\u{1B}[",
    String.append(codes, String.append("m", after_text)))
  +next_out = String.append(out, source)
  step_shape = scan_string_cong(raw, shaped, Cli.StripPlain{out},
    paint_append_shape(codes, source, suffix))
  step_styles = body_skip_first(style, styles, after_text, out,
    "\u{1B}[")
  step_text = plain_skip_free(source, after_reset, out, free)
  step_reset = reset_skip(suffix, next_out)
  Equal.trans(String,
    Cli.strip_fuel(Nat.add(1n, String.length(raw)),
      Cli.StripPlain{out}, raw),
    Cli.strip_fuel(Nat.add(1n, String.length(shaped)),
      Cli.StripPlain{out}, shaped),
    Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
      Cli.StripPlain{next_out}, suffix),
    step_shape,
    Equal.trans(String,
      Cli.strip_fuel(Nat.add(1n, String.length(shaped)),
        Cli.StripPlain{out}, shaped),
      Cli.strip_fuel(Nat.add(1n, String.length(after_text)),
        Cli.StripPlain{out}, after_text),
      Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
        Cli.StripPlain{next_out}, suffix),
      step_styles,
      Equal.trans(String,
        Cli.strip_fuel(Nat.add(1n, String.length(after_text)),
          Cli.StripPlain{out}, after_text),
        Cli.strip_fuel(Nat.add(1n, String.length(after_reset)),
          Cli.StripPlain{next_out}, after_reset),
        Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
          Cli.StripPlain{next_out}, suffix),
        step_text, step_reset)))

def paint_skip(styles: List<&2, Cli.Style>, +source: String,
    +suffix: String, +out: String, free: EscFree(source)) ->
    {Cli.strip_fuel(Nat.add(1n, String.length(
        String.append(Cli.paint(True{}, styles, source), suffix))),
      Cli.StripPlain{out},
      String.append(Cli.paint(True{}, styles, source), suffix))
      == Cli.strip_fuel(Nat.add(1n, String.length(suffix)),
        Cli.StripPlain{String.append(out, source)}, suffix) : String}:
  match styles:
    case Nil{}:
      plain_skip_free(source, suffix, out, free)
    case head <> tail:
      paint_skip_colored(head, tail, source, suffix, out, free)

def emit_strip_free(segments: List<&2, Cli.Segment>, +out: String,
    free: EscFree(Cli.emit(False{}, segments))) ->
    {Cli.strip_fuel(Nat.add(1n, String.length(Cli.emit(True{}, segments))),
      Cli.StripPlain{out}, Cli.emit(True{}, segments))
      == String.append(out, Cli.emit(False{}, segments)) : String}:
  match segments:
    case Nil{}:
      Equal.sym(String, String.append(out, ""), out, append_nil(out))
    case Cli.Segment{+source, styles} <> +rest:
      +styled_tail = Cli.emit(True{}, rest)
      +plain_tail = Cli.emit(False{}, rest)
      +next_out = String.append(out, source)
      pair_elim(EscFree(source), EscFree(plain_tail),
        {Cli.strip_fuel(Nat.add(1n, String.length(
            String.append(Cli.paint(True{}, styles, source), styled_tail))),
          Cli.StripPlain{out},
          String.append(Cli.paint(True{}, styles, source), styled_tail))
          == String.append(out, String.append(source, plain_tail)) : String},
        free_append_parts(source, plain_tail, free),
        source_free => rest_free =>
          Equal.trans(String,
            Cli.strip_fuel(Nat.add(1n, String.length(
                String.append(Cli.paint(True{}, styles, source), styled_tail))),
              Cli.StripPlain{out},
              String.append(Cli.paint(True{}, styles, source), styled_tail)),
            Cli.strip_fuel(Nat.add(1n, String.length(styled_tail)),
              Cli.StripPlain{next_out}, styled_tail),
            String.append(out, String.append(source, plain_tail)),
            paint_skip(styles, source, styled_tail, out, source_free),
            Equal.trans(String,
              Cli.strip_fuel(Nat.add(1n, String.length(styled_tail)),
                Cli.StripPlain{next_out}, styled_tail),
              String.append(next_out, plain_tail),
              String.append(out, String.append(source, plain_tail)),
              emit_strip_free(rest, next_out, rest_free),
              append_assoc(out, source, plain_tail))))

def strip_no_esc(+s: String,
    prem: {String.contains(s, "\u{1B}") == False{} : Bool}) ->
    {Cli.strip(s) == s : String}:
  Equal.trans(String,
    Cli.strip(s),
    Cli.strip_fuel(Nat.add(1n, String.length(String.append(s, ""))),
      Cli.StripPlain{""}, String.append(s, "")),
    s,
    scan_string_cong(s, String.append(s, ""), Cli.StripPlain{""},
      Equal.sym(String, String.append(s, ""), s, append_nil(s))),
    plain_skip_free(s, "", "", free_of_contains(s, prem)))

def paint_strip_no_esc(on: Bool, styles: List<&2, Cli.Style>, +s: String,
    prem: {String.contains(s, "\u{1B}") == False{} : Bool}) ->
    {Cli.strip(Cli.paint(on, styles, s)) == s : String}:
  match on styles:
    case False{} _:
      strip_no_esc(s, prem)
    case True{} Nil{}:
      strip_no_esc(s, prem)
    case True{} +h <> +t:
      Equal.trans(String,
        Cli.strip_fuel(Nat.add(1n, String.length(
          String.append(String.append(Cli.style_code(h),
            Cli.style_codes_tail(t)),
            String.append("m", String.append(s, "\u{1B}[0m"))))),
          Cli.StripBody{"", "\u{1B}["},
          String.append(String.append(Cli.style_code(h),
            Cli.style_codes_tail(t)),
            String.append("m", String.append(s, "\u{1B}[0m")))),
        Cli.strip_fuel(Nat.add(1n, String.length(
          String.append(s, "\u{1B}[0m"))), Cli.StripPlain{""},
          String.append(s, "\u{1B}[0m")), s,
        body_skip_first(h, t, String.append(s, "\u{1B}[0m"),
          "", "\u{1B}["),
        strip_reset_free(s, "", free_of_contains(s, prem)))

def Laws.p1(on, styles, s):
  ({==}, (prem => paint_strip_no_esc(on, styles, s, prem)))

def Laws.p2(segments):
  prem => emit_strip_free(segments, "",
    free_of_contains(Cli.emit(False{}, segments), prem))

def split_fin_append(c: Char, head: String,
    tail: List<&2, String>, ys: List<&2, String>, cut: Bool) ->
    {String.split.fin(c, List.append(&2, String, head <> tail, ys), cut)
      == List.append(&2, String,
        String.split.fin(c, head <> tail, cut), ys)
      : List<&2, String>}:
  match cut:
    case False{}: {==}
    case True{}: {==}

def NonEmpty(xs: List<&2, String>) -> Data:
  match xs:
    case Nil{}: Empty
    case head <> tail: Unit

def fin_nonempty(c: Char, xs: List<&2, String>, cut: Bool) ->
    NonEmpty(String.split.fin(c, xs, cut)):
  match xs cut:
    case Nil{} False{}: Unit{}
    case Nil{} True{}: Unit{}
    case head <> tail False{}: Unit{}
    case head <> tail True{}: Unit{}

def split_nonempty(s: String, +sep: Char) ->
    NonEmpty(String.split(s, sep)):
  match s:
    case SNil{}: Unit{}
    case SCon{+head, tail}:
      fin_nonempty(head, String.split(tail, sep), Char.is_eq(head, sep))

def split_fin_append_nonempty(c: Char, xs: List<&2, String>,
    ys: List<&2, String>, cut: Bool, non: NonEmpty(xs)) ->
    {String.split.fin(c, List.append(&2, String, xs, ys), cut)
      == List.append(&2, String, String.split.fin(c, xs, cut), ys)
      : List<&2, String>}:
  match xs:
    case Nil{}:
      Empty.absurd({String.split.fin(c, List.append(&2, String, Nil{}, ys), cut)
        == List.append(&2, String, String.split.fin(c, Nil{}, cut), ys)
        : List<&2, String>}, non)
    case head <> tail:
      split_fin_append(c, head, tail, ys, cut)

def split_append_newline(s: String, +t: String) ->
    {String.lines(String.append(s, String.append("\n", t)))
      == List.append(&2, String, String.lines(s), String.lines(t))
      : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+head, +tail}:
      Equal.trans(List<&2, String>,
        String.split.fin(head,
          String.lines(String.append(tail, String.append("\n", t))),
          Char.is_eq(head, '\n')),
        String.split.fin(head,
          List.append(&2, String, String.lines(tail), String.lines(t)),
          Char.is_eq(head, '\n')),
        List.append(&2, String,
          String.split.fin(head, String.lines(tail), Char.is_eq(head, '\n')),
          String.lines(t)),
        Equal.cong(List<&2, String>, List<&2, String>,
          xs => String.split.fin(head, xs, Char.is_eq(head, '\n')),
          String.lines(String.append(tail, String.append("\n", t))),
          List.append(&2, String, String.lines(tail), String.lines(t)),
          split_append_newline(tail, t)),
        split_fin_append_nonempty(head, String.lines(tail),
          String.lines(t), Char.is_eq(head, '\n'),
          split_nonempty(tail, '\n')))

def NoNL(s: String) -> Type:
  match s:
    case SNil{}: Unit
    case SCon{head, tail}:
      {Char.is_eq(head, '\n') == False{} : Bool} & NoNL(tail)

def lines_nolf(s: String, prem: NoNL(s)) ->
    {String.lines(s) == [s] : List<&2, String>}:
  match s:
    case SNil{}: {==}
    case SCon{+head, +tail}:
      pair_elim({Char.is_eq(head, '\n') == False{} : Bool}, NoNL(tail),
        {String.lines(SCon{head, tail}) == [SCon{head, tail}]
          : List<&2, String>},
        prem, head_no => tail_no =>
          Equal.trans(List<&2, String>,
            String.split.fin(head, String.lines(tail), Char.is_eq(head, '\n')),
            String.split.fin(head, [tail], Char.is_eq(head, '\n')),
            [SCon{head, tail}],
            Equal.cong(List<&2, String>, List<&2, String>,
              xs => String.split.fin(head, xs, Char.is_eq(head, '\n')),
              String.lines(tail), [tail], lines_nolf(tail, tail_no)),
            Equal.cong(Bool, List<&2, String>,
              cut => String.split.fin(head, [tail], cut),
              Char.is_eq(head, '\n'), False{}, head_no)))

def flatten_lines(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}: Nil{}
    case head <> tail:
      List.append(&2, String, String.lines(head), flatten_lines(tail))

def list_append_nil(xs: List<&2, String>) ->
    {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case head <> tail:
      Equal.cong(List<&2, String>, List<&2, String>,
        rest => head <> rest,
        List.append(&2, String, tail, Nil{}), tail,
        list_append_nil(tail))

def join_go_lines(xs: List<&2, String>, +head: String) ->
    {String.lines(String.join.go(xs, head, "\n"))
      == List.append(&2, String, String.lines(head), flatten_lines(xs))
      : List<&2, String>}:
  match xs:
    case Nil{}:
      Equal.sym(List<&2, String>,
        List.append(&2, String, String.lines(head), Nil{}),
        String.lines(head), list_append_nil(String.lines(head)))
    case +next <> +tail:
      Equal.trans(List<&2, String>,
        String.lines(String.append(head, String.append("\n",
          String.join.go(tail, next, "\n")))),
        List.append(&2, String, String.lines(head),
          String.lines(String.join.go(tail, next, "\n"))),
        List.append(&2, String, String.lines(head),
          List.append(&2, String, String.lines(next), flatten_lines(tail))),
        split_append_newline(head, String.join.go(tail, next, "\n")),
        Equal.cong(List<&2, String>, List<&2, String>,
          rest => List.append(&2, String, String.lines(head), rest),
          String.lines(String.join.go(tail, next, "\n")),
          List.append(&2, String, String.lines(next), flatten_lines(tail)),
          join_go_lines(tail, next)))

def join_lines_nonempty(head: String, tail: List<&2, String>) ->
    {String.lines(String.join(head <> tail, "\n"))
      == flatten_lines(head <> tail) : List<&2, String>}:
  join_go_lines(tail, head)

def LineGood(cols: Nat, +line: String) -> Bool:
  Bool.or(Nat.is_le(Cli.width(Cli.strip(line)), cols),
    Nat.is_le(List.length(&2, String,
      List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
        String.split(line, ' '))), 1n))

def and_true_parts(a: Bool, b: Bool,
    e: {Bool.and(a, b) == True{} : Bool}) ->
    ({a == True{} : Bool} & {b == True{} : Bool}):
  match a b:
    case False{} _:
      Empty.absurd({False{} == True{} : Bool} &
        {b == True{} : Bool}, true_false_absurd(
          Equal.sym(Bool, False{}, True{}, e)))
    case True{} False{}:
      Empty.absurd({True{} == True{} : Bool} &
        {False{} == True{} : Bool}, true_false_absurd(
          Equal.sym(Bool, False{}, True{}, e)))
    case True{} True{}:
      ({==}, {==})

def and_true(a: Bool, b: Bool,
    ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) ->
    {Bool.and(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(a, b), Bool.and(True{}, b), True{},
    Equal.cong(Bool, Bool, x => Bool.and(x, b), a, True{}, ea), eb)

def NoSpace(s: String) -> Type:
  match s:
    case SNil{}: Unit
    case SCon{head, tail}:
      {Char.is_eq(head, ' ') == False{} : Bool} & NoSpace(tail)

def split_nospace(s: String, prem: NoSpace(s)) ->
    {String.split(s, ' ') == [s] : List<&2, String>}:
  match s:
    case SNil{}: {==}
    case SCon{+head, +tail}:
      pair_elim({Char.is_eq(head, ' ') == False{} : Bool}, NoSpace(tail),
        {String.split(SCon{head, tail}, ' ') == [SCon{head, tail}]
          : List<&2, String>},
        prem, head_no => tail_no =>
          Equal.trans(List<&2, String>,
            String.split.fin(head, String.split(tail, ' '),
              Char.is_eq(head, ' ')),
            String.split.fin(head, [tail], Char.is_eq(head, ' ')),
            [SCon{head, tail}],
            Equal.cong(List<&2, String>, List<&2, String>,
              xs => String.split.fin(head, xs, Char.is_eq(head, ' ')),
              String.split(tail, ' '), [tail], split_nospace(tail, tail_no)),
            Equal.cong(Bool, List<&2, String>,
              cut => String.split.fin(head, [tail], cut),
              Char.is_eq(head, ' '), False{}, head_no)))

def Spaces(s: String) -> Type:
  match s:
    case SNil{}: Unit
    case SCon{head, tail}:
      {Char.is_eq(head, ' ') == True{} : Bool} & Spaces(tail)

def copy_spaces(s: String, p: Spaces(s)) -> Spaces(s) & Spaces(s):
  match s:
    case SNil{}: (Unit{}, Unit{})
    case SCon{head, tail}:
      pair_elim({Char.is_eq(head, ' ') == True{} : Bool}, Spaces(tail),
        Spaces(SCon{head, tail}) & Spaces(SCon{head, tail}), p,
        +eh => et =>
          pair_elim(Spaces(tail), Spaces(tail),
            Spaces(SCon{head, tail}) & Spaces(SCon{head, tail}),
            copy_spaces(tail, et), left => right =>
              ((eh, left), (eh, right))))

def nonempty_words(s: String) -> List<&2, String>:
  List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
    String.split(s, ' '))

def count_single(s: String) ->
    {Nat.is_le(List.length(&2, String,
      List.filter(~String, ~(w => Bool.not(String.is_empty(w))), [s])),
      1n) == True{} : Bool}:
  match s:
    case SNil{}: {==}
    case SCon{head, tail}: {==}

def count_nospace(+s: String, prem: NoSpace(s)) ->
    {Nat.is_le(List.length(&2, String, nonempty_words(s)), 1n)
      == True{} : Bool}:
  Equal.trans(Bool,
    Nat.is_le(List.length(&2, String, nonempty_words(s)), 1n),
    Nat.is_le(List.length(&2, String,
      List.filter(~String, ~(w => Bool.not(String.is_empty(w))), [s])),
      1n), True{},
    Equal.cong(List<&2, String>, Bool,
      xs => Nat.is_le(List.length(&2, String,
        List.filter(~String, ~(w => Bool.not(String.is_empty(w))), xs)),
        1n),
      String.split(s, ' '), [s], split_nospace(s, prem)),
    count_single(s))

def count_spaced(indent: String, +word: String,
    spaces: Spaces(indent), clean: NoSpace(word)) ->
    {Nat.is_le(List.length(&2, String,
      nonempty_words(String.append(indent, word))), 1n)
      == True{} : Bool}:
  match indent:
    case SNil{}:
      count_nospace(word, clean)
    case SCon{+head, +tail}:
      pair_elim({Char.is_eq(head, ' ') == True{} : Bool}, Spaces(tail),
        {Nat.is_le(List.length(&2, String,
          nonempty_words(String.append(SCon{head, tail}, word))), 1n)
          == True{} : Bool},
        spaces, head_space => tail_spaces =>
          Equal.trans(Bool,
            Nat.is_le(List.length(&2, String,
              nonempty_words(String.append(SCon{head, tail}, word))), 1n),
            Nat.is_le(List.length(&2, String,
              nonempty_words(String.append(tail, word))), 1n),
            True{},
            Equal.cong(Bool, Bool,
              cut => Nat.is_le(List.length(&2, String,
                List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
                  String.split.fin(head,
                    String.split(String.append(tail, word), ' '), cut))),
                1n),
              Char.is_eq(head, ' '), True{}, head_space),
            count_spaced(tail, word, tail_spaces, clean)))

def AllNoSpace(xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}: Unit
    case head <> tail: NoSpace(head) & AllNoSpace(tail)

def push_nospace(c: Char, xs: List<&2, String>,
    head_no: {Char.is_eq(c, ' ') == False{} : Bool},
    clean: AllNoSpace(xs)) -> AllNoSpace(String.split.push(c, xs)):
  match xs:
    case Nil{}: ((head_no, Unit{}), Unit{})
    case head <> tail:
      pair_elim(NoSpace(head), AllNoSpace(tail),
        AllNoSpace(String.split.push(c, head <> tail)),
        clean, eh => et => ((head_no, eh), et))

def fin_nospace(c: Char, xs: List<&2, String>, cut: Bool,
    clean: AllNoSpace(xs),
    head_no: {cut == False{} : Bool} ->
      {Char.is_eq(c, ' ') == False{} : Bool}) ->
    AllNoSpace(String.split.fin(c, xs, cut)):
  match cut:
    case False{}:
      push_nospace(c, xs, head_no({==}), clean)
    case True{}:
      (Unit{}, clean)

def split_all_nospace(s: String) -> AllNoSpace(String.split(s, ' ')):
  match s:
    case SNil{}: (Unit{}, Unit{})
    case SCon{+head, +tail}:
      fin_nospace(head, String.split(tail, ' '), Char.is_eq(head, ' '),
        split_all_nospace(tail), p => p)

def filter_nospace_put(head: String, tail: List<&2, String>,
    keep: Bool, clean_head: NoSpace(head),
    clean_tail: AllNoSpace(tail)) ->
    AllNoSpace(List.filter.put(String, head, tail, keep)):
  match keep:
    case False{}: clean_tail
    case True{}: (clean_head, clean_tail)

def filter_all_nospace(xs: List<&2, String>,
    clean: AllNoSpace(xs)) ->
    AllNoSpace(List.filter(~String,
      ~(w => Bool.not(String.is_empty(w))), xs)):
  match xs:
    case Nil{}: Unit{}
    case +head <> +tail:
      pair_elim(NoSpace(head), AllNoSpace(tail),
        AllNoSpace(List.filter(~String,
          ~(w => Bool.not(String.is_empty(w))), head <> tail)),
        clean, eh => et =>
          filter_nospace_put(head,
            List.filter(~String, ~(w => Bool.not(String.is_empty(w))), tail),
            Bool.not(String.is_empty(head)), eh,
            filter_all_nospace(tail, et)))

def indent_spaces_fin(head: Char, tail: String, cut: Bool,
    rec: Spaces(Cli.leading_indent(tail)),
    eq: {cut == Char.is_eq(head, ' ') : Bool}) ->
    Spaces(Bool.pick(String, cut,
      SCon{head, Cli.leading_indent(tail)}, "")):
  match cut:
    case False{}: Unit{}
    case True{}:
      (Equal.sym(Bool, True{}, Char.is_eq(head, ' '), eq), rec)

def indent_spaces(s: String) -> Spaces(Cli.leading_indent(s)):
  match s:
    case SNil{}: Unit{}
    case SCon{+head, +tail}:
      indent_spaces_fin(head, tail, Char.is_eq(head, ' '),
        indent_spaces(tail), {==})

def indent_nonl_fin(head: Char, tail: String, cut: Bool,
    head_no: {Char.is_eq(head, '\n') == False{} : Bool},
    rec: NoNL(Cli.leading_indent(tail))) ->
    NoNL(Bool.pick(String, cut,
      SCon{head, Cli.leading_indent(tail)}, "")):
  match cut:
    case False{}: Unit{}
    case True{}: (head_no, rec)

def indent_nonl(s: String, clean: NoNL(s)) ->
    NoNL(Cli.leading_indent(s)):
  match s:
    case SNil{}: Unit{}
    case SCon{+head, +tail}:
      pair_elim({Char.is_eq(head, '\n') == False{} : Bool}, NoNL(tail),
        NoNL(Cli.leading_indent(SCon{head, tail})), clean,
        eh => et => indent_nonl_fin(head, tail, Char.is_eq(head, ' '),
          eh, indent_nonl(tail, et)))

def AllNoNL(xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}: Unit
    case head <> tail: NoNL(head) & AllNoNL(tail)

def push_nonl(c: Char, xs: List<&2, String>,
    head_no: {Char.is_eq(c, '\n') == False{} : Bool},
    clean: AllNoNL(xs)) -> AllNoNL(String.split.push(c, xs)):
  match xs:
    case Nil{}: ((head_no, Unit{}), Unit{})
    case head <> tail:
      pair_elim(NoNL(head), AllNoNL(tail),
        AllNoNL(String.split.push(c, head <> tail)),
        clean, eh => et => ((head_no, eh), et))

def fin_nonl(c: Char, xs: List<&2, String>, cut: Bool,
    clean: AllNoNL(xs),
    head_no: {cut == False{} : Bool} ->
      {Char.is_eq(c, '\n') == False{} : Bool}) ->
    AllNoNL(String.split.fin(c, xs, cut)):
  match cut:
    case False{}: push_nonl(c, xs, head_no({==}), clean)
    case True{}: (Unit{}, clean)

def lines_all_nonl(s: String) -> AllNoNL(String.lines(s)):
  match s:
    case SNil{}: (Unit{}, Unit{})
    case SCon{+head, +tail}:
      fin_nonl(head, String.lines(tail), Char.is_eq(head, '\n'),
        lines_all_nonl(tail), p => p)

def drop_nonl(s: String, n: Nat, clean: NoNL(s)) ->
    NoNL(String.drop(s, n)):
  match s n:
    case SNil{} _:
      Unit{}
    case SCon{head, tail} 0n:
      clean
    case SCon{head, tail} 1n+p:
      pair_elim({Char.is_eq(head, '\n') == False{} : Bool},
        NoNL(tail), NoNL(String.drop(SCon{head, tail}, 1n+p)),
        clean, eh => et => drop_nonl(tail, p, et))

def fin_space_nonl(c: Char, xs: List<&2, String>, cut: Bool,
    head_no: {Char.is_eq(c, '\n') == False{} : Bool},
    clean: AllNoNL(xs)) -> AllNoNL(String.split.fin(c, xs, cut)):
  match cut:
    case False{}: push_nonl(c, xs, head_no, clean)
    case True{}: (Unit{}, clean)

def split_space_nonl(s: String, clean: NoNL(s)) ->
    AllNoNL(String.split(s, ' ')):
  match s:
    case SNil{}: (Unit{}, Unit{})
    case SCon{+head, +tail}:
      pair_elim({Char.is_eq(head, '\n') == False{} : Bool}, NoNL(tail),
        AllNoNL(String.split(SCon{head, tail}, ' ')), clean,
        eh => et => fin_space_nonl(head, String.split(tail, ' '),
          Char.is_eq(head, ' '), eh, split_space_nonl(tail, et)))

def filter_nonl_put(head: String, tail: List<&2, String>,
    keep: Bool, clean_head: NoNL(head),
    clean_tail: AllNoNL(tail)) ->
    AllNoNL(List.filter.put(String, head, tail, keep)):
  match keep:
    case False{}: clean_tail
    case True{}: (clean_head, clean_tail)

def filter_all_nonl(xs: List<&2, String>, clean: AllNoNL(xs)) ->
    AllNoNL(List.filter(~String,
      ~(w => Bool.not(String.is_empty(w))), xs)):
  match xs:
    case Nil{}: Unit{}
    case +head <> +tail:
      pair_elim(NoNL(head), AllNoNL(tail),
        AllNoNL(List.filter(~String,
          ~(w => Bool.not(String.is_empty(w))), head <> tail)),
        clean, eh => et =>
          filter_nonl_put(head,
            List.filter(~String, ~(w => Bool.not(String.is_empty(w))), tail),
            Bool.not(String.is_empty(head)), eh,
            filter_all_nonl(tail, et)))

def AllGood(cols: Nat, xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}: Unit
    case head <> tail:
      {LineGood(cols, head) == True{} : Bool} & AllGood(cols, tail)

def append_nonl(a: String, b: String, pa: NoNL(a), pb: NoNL(b)) ->
    NoNL(String.append(a, b)):
  match a:
    case SNil{}: pb
    case SCon{head, tail}:
      pair_elim({Char.is_eq(head, '\n') == False{} : Bool}, NoNL(tail),
        NoNL(String.append(SCon{head, tail}, b)),
        pa, eh => et => (eh, append_nonl(tail, b, et, pb)))

def copy_nonl(s: String, p: NoNL(s)) -> NoNL(s) & NoNL(s):
  match s:
    case SNil{}: (Unit{}, Unit{})
    case SCon{head, tail}:
      pair_elim({Char.is_eq(head, '\n') == False{} : Bool}, NoNL(tail),
        NoNL(SCon{head, tail}) & NoNL(SCon{head, tail}), p,
        +eh => et =>
          pair_elim(NoNL(tail), NoNL(tail),
            NoNL(SCon{head, tail}) & NoNL(SCon{head, tail}),
            copy_nonl(tail, et), left => right =>
              ((eh, left), (eh, right))))

def SafeLine(cols: Nat, line: String) -> Type:
  {LineGood(cols, line) == True{} : Bool} & NoNL(line)

def SafeLines(cols: Nat, lines: List<&2, String>) -> Type:
  match lines:
    case Nil{}: Unit
    case head <> tail: SafeLine(cols, head) & SafeLines(cols, tail)

def safe_reverse_go(cols: Nat, xs: List<&2, String>,
    acc: List<&2, String>, px: SafeLines(cols, xs),
    pa: SafeLines(cols, acc)) ->
    SafeLines(cols, List.reverse.go(&2, String, xs, acc)):
  match xs:
    case Nil{}: pa
    case head <> tail:
      pair_elim(SafeLine(cols, head), SafeLines(cols, tail),
        SafeLines(cols, List.reverse.go(&2, String, head <> tail, acc)),
        px, eh => et => safe_reverse_go(cols, tail, head <> acc,
          et, (eh, pa)))

def reverse_go_nonempty(xs: List<&2, String>,
    acc: List<&2, String>, non: NonEmpty(acc)) ->
    NonEmpty(List.reverse.go(&2, String, xs, acc)):
  match xs:
    case Nil{}: non
    case head <> tail:
      reverse_go_nonempty(tail, head <> acc, Unit{})

def reverse_nonempty(head: String, tail: List<&2, String>) ->
    NonEmpty(List.reverse(&2, String, head <> tail)):
  reverse_go_nonempty(tail, head <> Nil{}, Unit{})

def or_true_right(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case False{}: {==}
    case True{}: {==}

def line_good_single(cols: Nat, +indent: String, +word: String,
    spaces: Spaces(indent), clean: NoSpace(word)) ->
    {LineGood(cols, String.append(indent, word)) == True{} : Bool}:
  Equal.trans(Bool,
    LineGood(cols, String.append(indent, word)),
    Bool.or(Nat.is_le(Cli.width(Cli.strip(String.append(indent, word))), cols),
      True{}), True{},
    Equal.cong(Bool, Bool,
      count => Bool.or(
        Nat.is_le(Cli.width(Cli.strip(String.append(indent, word))), cols),
        count),
      Nat.is_le(List.length(&2, String,
        nonempty_words(String.append(indent, word))), 1n),
      True{}, count_spaced(indent, word, spaces, clean)),
    or_true_right(Nat.is_le(
      Cli.width(Cli.strip(String.append(indent, word))), cols)))

def line_good_fit(cols: Nat, line: String,
    fit: {Nat.is_le(Cli.width(Cli.strip(line)), cols) == True{} : Bool}) ->
    {LineGood(cols, line) == True{} : Bool}:
  Equal.cong(Bool, Bool,
    b => Bool.or(b, Nat.is_le(List.length(&2, String,
      nonempty_words(line)), 1n)),
    Nat.is_le(Cli.width(Cli.strip(line)), cols), True{}, fit)

def empty_good(cols: Nat) -> {LineGood(cols, "") == True{} : Bool}:
  match cols:
    case 0n: {==}
    case 1n+p: {==}

def LineIf(started: Bool, cols: Nat, line: String) -> Type:
  match started:
    case False{}: Unit
    case True{}: {LineGood(cols, line) == True{} : Bool}

def wrap_lines_nonempty(lines: List<&2, String>, cols: Nat,
    non: NonEmpty(lines)) ->
    NonEmpty(Cli.wrap_lines(lines, cols)):
  match lines:
    case Nil{}:
      Empty.absurd(NonEmpty(Cli.wrap_lines(Nil{}, cols)), non)
    case head <> tail:
      Unit{}

def p13_bool(+cols: Nat, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: True{}
    case head <> tail:
      Bool.and(LineGood(cols, head), p13_bool(cols, tail))

def allgood_append(cols: Nat, xs: List<&2, String>,
    ys: List<&2, String>, px: AllGood(cols, xs),
    py: AllGood(cols, ys)) ->
    AllGood(cols, List.append(&2, String, xs, ys)):
  match xs:
    case Nil{}: py
    case head <> tail:
      pair_elim({LineGood(cols, head) == True{} : Bool}, AllGood(cols, tail),
        AllGood(cols, List.append(&2, String, head <> tail, ys)), px,
        eh => et => (eh, allgood_append(cols, tail, ys, et, py)))

def safe_line_good_lines(cols: Nat, line: String,
    safe: SafeLine(cols, line)) -> AllGood(cols, String.lines(line)):
  pair_elim({LineGood(cols, line) == True{} : Bool}, NoNL(line),
    AllGood(cols, String.lines(line)), safe,
    good => nonl =>
      %Equal.sym(List<&2, String>, String.lines(line), [line],
        lines_nolf(line, nonl)) : AllGood(cols, _)
      (good, Unit{}))

def safe_flatten_good(+cols: Nat, xs: List<&2, String>,
    safe: SafeLines(cols, xs)) -> AllGood(cols, flatten_lines(xs)):
  match xs:
    case Nil{}: Unit{}
    case +head <> +tail:
      pair_elim(SafeLine(cols, head), SafeLines(cols, tail),
        AllGood(cols, flatten_lines(head <> tail)), safe,
        eh => et => allgood_append(cols, String.lines(head),
          flatten_lines(tail), safe_line_good_lines(cols, head, eh),
          safe_flatten_good(cols, tail, et)))

def allgood_to_p13_bool(+cols: Nat, xs: List<&2, String>,
    good: AllGood(cols, xs)) ->
    {p13_bool(cols, xs) == True{} : Bool}:
  match xs:
    case Nil{}: {==}
    case +head <> +tail:
      pair_elim({LineGood(cols, head) == True{} : Bool}, AllGood(cols, tail),
        {p13_bool(cols, head <> tail) == True{} : Bool}, good,
        eh => et => and_true(LineGood(cols, head), p13_bool(cols, tail),
          eh, allgood_to_p13_bool(cols, tail, et)))

def join_safe_p13(+cols: Nat, xs: List<&2, String>,
    non: NonEmpty(xs), safe: SafeLines(cols, xs)) ->
    {p13_bool(cols, String.lines(String.join(xs, "\n")))
      == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({p13_bool(cols,
        String.lines(String.join(Nil{}, "\n"))) == True{} : Bool}, non)
    case +head <> +tail:
      %Equal.sym(List<&2, String>,
        String.lines(String.join(head <> tail, "\n")),
        flatten_lines(head <> tail), join_lines_nonempty(head, tail))
        : {p13_bool(cols, _) == True{} : Bool}
      allgood_to_p13_bool(cols, flatten_lines(head <> tail),
        safe_flatten_good(cols, head <> tail, safe))

def ChunkGood(cols: Nat, xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}: Unit
    case head <> tail:
      AllGood(cols, String.lines(head)) & ChunkGood(cols, tail)

def good_flatten_chunks(+cols: Nat, xs: List<&2, String>,
    good: ChunkGood(cols, xs)) -> AllGood(cols, flatten_lines(xs)):
  match xs:
    case Nil{}: Unit{}
    case +head <> +tail:
      pair_elim(AllGood(cols, String.lines(head)), ChunkGood(cols, tail),
        AllGood(cols, flatten_lines(head <> tail)), good,
        eh => et => allgood_append(cols, String.lines(head),
          flatten_lines(tail), eh, good_flatten_chunks(cols, tail, et)))

def join_chunks_p13(+cols: Nat, xs: List<&2, String>,
    non: NonEmpty(xs), chunks: ChunkGood(cols, xs)) ->
    {p13_bool(cols, String.lines(String.join(xs, "\n")))
      == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({p13_bool(cols,
        String.lines(String.join(Nil{}, "\n"))) == True{} : Bool}, non)
    case +head <> +tail:
      %Equal.sym(List<&2, String>,
        String.lines(String.join(head <> tail, "\n")),
        flatten_lines(head <> tail), join_lines_nonempty(head, tail))
        : {p13_bool(cols, _) == True{} : Bool}
      allgood_to_p13_bool(cols, flatten_lines(head <> tail),
        good_flatten_chunks(cols, head <> tail, chunks))

def p13_bool_to_allgood(+cols: Nat, xs: List<&2, String>,
    good: {p13_bool(cols, xs) == True{} : Bool}) -> AllGood(cols, xs):
  match xs:
    case Nil{}: Unit{}
    case +head <> +tail:
      pair_elim({LineGood(cols, head) == True{} : Bool},
        {p13_bool(cols, tail) == True{} : Bool}, AllGood(cols, head <> tail),
        and_true_parts(LineGood(cols, head), p13_bool(cols, tail), good),
        eh => et => (eh, p13_bool_to_allgood(cols, tail, et)))

def allgood_transport(cols: Nat, xs: List<&2, String>,
    ys: List<&2, String>, eq: {xs == ys : List<&2, String>},
    good: AllGood(cols, xs)) -> AllGood(cols, ys):
  %eq : AllGood(cols, _)
  good

def wrap_result_cong_all(+cols: Nat,
    +words: List<&2, String>, +yes: Cli.WrapState, +no: Cli.WrapState,
    a: Bool, b: Bool, eq: {a == b : Bool},
    good: AllGood(cols, String.lines(Cli.wrap_words(words,
      Bool.pick(Cli.WrapState, a, yes, no))))) ->
    AllGood(cols, String.lines(Cli.wrap_words(words,
      Bool.pick(Cli.WrapState, b, yes, no)))):
  allgood_transport(cols,
    String.lines(Cli.wrap_words(words,
      Bool.pick(Cli.WrapState, a, yes, no))),
    String.lines(Cli.wrap_words(words,
      Bool.pick(Cli.WrapState, b, yes, no))),
    Equal.cong(Bool, List<&2, String>,
      cut => String.lines(Cli.wrap_words(words,
        Bool.pick(Cli.WrapState, cut, yes, no))), a, b, eq), good)

def WrapGoalAll(+cols: Nat, words: List<&2, String>,
    indent: String, line: String, started: Bool,
    done: List<&2, String>) -> Type:
  AllGood(cols, String.lines(Cli.wrap_words(words,
    Cli.WrapState{indent, cols, line, started, done})))

def wrap_base_all(+cols: Nat, +line: String, started: Bool,
    +done: List<&2, String>, line_if: LineIf(started, cols, line),
    line_no: NoNL(line), done_safe: SafeLines(cols, done)) ->
    AllGood(cols, String.lines(Bool.pick(String, started,
      String.join(List.reverse(&2, String, line <> done), "\n"), ""))):
  match started:
    case False{}:
      p13_bool_to_allgood(cols, String.lines(""),
        join_safe_p13(cols, [""], Unit{},
          ((empty_good(cols), Unit{}), Unit{})))
    case True{}:
      p13_bool_to_allgood(cols,
        String.lines(String.join(List.reverse(&2, String,
          line <> done), "\n")),
        join_safe_p13(cols, List.reverse(&2, String, line <> done),
          reverse_nonempty(line, done),
          safe_reverse_go(cols, line <> done, Nil{},
            ((line_if, line_no), done_safe), Unit{})))

def wrap_false_step_all(cols: Nat, word: String,
    rest: List<&2, String>, indent: String, line: String,
    done: List<&2, String>,
    rec: WrapGoalAll(cols, rest, indent,
      String.append(indent, word), True{}, done)) ->
    WrapGoalAll(cols, word <> rest, indent, line, False{}, done):
  rec

def WrapRecAll(cols: Nat, rest: List<&2, String>,
    indent: String) -> Type:
  @next_line:String -> @next_done:List<&2, String> ->
    Spaces(indent) -> NoNL(indent) -> NoNL(next_line) ->
    SafeLines(cols, next_done) ->
    {LineGood(cols, next_line) == True{} : Bool} ->
    WrapGoalAll(cols, rest, indent, next_line, True{}, next_done)

def wrap_false_fin_all(+cols: Nat,
    +word: String, +rest: List<&2, String>, +indent: String,
    line: String, +done: List<&2, String>,
    spaces: Spaces(indent), indent_no: NoNL(indent),
    word_clean: NoSpace(word), word_no: NoNL(word),
    done_safe: SafeLines(cols, done),
    rec: WrapRecAll(cols, rest, indent)) ->
    WrapGoalAll(cols, word <> rest, indent, line, False{}, done):
  pair_elim(Spaces(indent), Spaces(indent),
    WrapGoalAll(cols, word <> rest, indent, line, False{}, done),
    copy_spaces(indent, spaces),
    spaces_1 => spaces_2 =>
      pair_elim(NoNL(indent), NoNL(indent),
        WrapGoalAll(cols, word <> rest, indent, line, False{}, done),
        copy_nonl(indent, indent_no),
        indent_no_1 => indent_no_2 =>
          wrap_false_step_all(cols, word, rest, indent, line, done,
            rec(String.append(indent, word))(done)(spaces_1)(indent_no_1)(
              append_nonl(indent, word, indent_no_2, word_no))(
              done_safe)(line_good_single(cols, indent, word,
                spaces_2, word_clean)))))

def wrap_true_fin_all(+cols: Nat,
    +word: String, +rest: List<&2, String>, +indent: String,
    +line: String, +done: List<&2, String>, fit: Bool,
    +eq: {fit == Nat.is_le(Cli.width(Cli.strip(
      String.append(line, String.append(" ", word)))), cols) : Bool},
    spaces: Spaces(indent), indent_no: NoNL(indent),
    line_no: NoNL(line), line_good: {LineGood(cols, line) == True{} : Bool},
    word_clean: NoSpace(word), word_no: NoNL(word),
    done_safe: SafeLines(cols, done),
    rec: WrapRecAll(cols, rest, indent)) ->
    WrapGoalAll(cols, word <> rest, indent, line, True{}, done):
  match fit:
    case False{}:
      pair_elim(Spaces(indent), Spaces(indent),
        WrapGoalAll(cols, word <> rest, indent, line, True{}, done),
        copy_spaces(indent, spaces),
        spaces_1 => spaces_2 =>
          pair_elim(NoNL(indent), NoNL(indent),
            WrapGoalAll(cols, word <> rest, indent, line, True{}, done),
            copy_nonl(indent, indent_no),
            indent_no_1 => indent_no_2 =>
              wrap_result_cong_all(cols, rest,
                Cli.WrapState{indent, cols,
                  String.append(line, String.append(" ", word)), True{}, done},
                Cli.WrapState{indent, cols, String.append(indent, word),
                  True{}, line <> done},
                False{}, Nat.is_le(Cli.width(Cli.strip(
                  String.append(line, String.append(" ", word)))), cols), eq,
                rec(String.append(indent, word))(line <> done)(
                  spaces_1)(indent_no_1)(
                  append_nonl(indent, word, indent_no_2, word_no))(
                  ((line_good, line_no), done_safe))(
                  line_good_single(cols, indent, word,
                    spaces_2, word_clean)))))
    case True{}:
      wrap_result_cong_all(cols, rest,
        Cli.WrapState{indent, cols,
          String.append(line, String.append(" ", word)), True{}, done},
        Cli.WrapState{indent, cols, String.append(indent, word),
          True{}, line <> done},
        True{}, Nat.is_le(Cli.width(Cli.strip(
          String.append(line, String.append(" ", word)))), cols), eq,
        rec(String.append(line, String.append(" ", word)))(done)(spaces)(
          indent_no)(append_nonl(line, String.append(" ", word), line_no,
            append_nonl(" ", word, ({==}, Unit{}), word_no)))(done_safe)(
          line_good_fit(cols, String.append(line, String.append(" ", word)),
            Equal.sym(Bool, True{},
              Nat.is_le(Cli.width(Cli.strip(
                String.append(line, String.append(" ", word)))), cols), eq))))

def wrap_words_all(+cols: Nat,
    words: List<&2, String>, +indent: String, +line: String,
    started: Bool, +done: List<&2, String>,
    spaces: Spaces(indent), indent_no: NoNL(indent),
    line_no: NoNL(line), done_safe: SafeLines(cols, done),
    line_if: LineIf(started, cols, line),
    words_clean: AllNoSpace(words), words_no: AllNoNL(words)) ->
    WrapGoalAll(cols, words, indent, line, started, done):
  match words started:
    case Nil{} started:
      wrap_base_all(cols, line, started, done,
        line_if, line_no, done_safe)
    case +word <> +rest False{}:
      (word_clean, rest_clean) = words_clean
      (word_no, rest_no) = words_no
      wrap_false_fin_all(cols, word, rest, indent, line, done,
        spaces, indent_no, word_clean, word_no, done_safe,
        next_line => next_done => next_spaces => next_indent_no =>
          next_line_no => next_done_safe => next_good =>
            wrap_words_all(cols, rest,
              indent, next_line, True{}, next_done,
              next_spaces, next_indent_no, next_line_no,
              next_done_safe, next_good, rest_clean, rest_no))
    case +word <> +rest True{}:
      (word_clean, rest_clean) = words_clean
      (word_no, rest_no) = words_no
      wrap_true_fin_all(cols, word, rest, indent, line, done,
        Nat.is_le(Cli.width(Cli.strip(
          String.append(line, String.append(" ", word)))), cols), {==},
        spaces, indent_no, line_no, line_if, word_clean, word_no,
        done_safe,
        next_line => next_done => next_spaces => next_indent_no =>
          next_line_no => next_done_safe => next_good =>
            wrap_words_all(cols, rest,
              indent, next_line, True{}, next_done,
              next_spaces, next_indent_no, next_line_no,
              next_done_safe, next_good, rest_clean, rest_no))

def wrap_line_all(+cols: Nat, +line: String, clean: NoNL(line)) ->
    AllGood(cols, String.lines(Cli.wrap_line(line, cols))):
  pair_elim(NoNL(line), NoNL(line),
    AllGood(cols, String.lines(Cli.wrap_line(line, cols))),
    copy_nonl(line, clean),
    clean_1 => clean_2 =>
      pair_elim(NoNL(Cli.leading_indent(line)),
        NoNL(Cli.leading_indent(line)),
        AllGood(cols, String.lines(Cli.wrap_line(line, cols))),
        copy_nonl(Cli.leading_indent(line), indent_nonl(line, clean_1)),
        indent_no => initial_line_no =>
          wrap_words_all(cols,
            List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
              String.split(String.drop(line,
                String.length(Cli.leading_indent(line))), ' ')),
            Cli.leading_indent(line), Cli.leading_indent(line),
            False{}, Nil{}, indent_spaces(line), indent_no,
            initial_line_no, Unit{}, Unit{},
            filter_all_nospace(String.split(String.drop(line,
              String.length(Cli.leading_indent(line))), ' '),
              split_all_nospace(String.drop(line,
                String.length(Cli.leading_indent(line))))),
            filter_all_nonl(String.split(String.drop(line,
              String.length(Cli.leading_indent(line))), ' '),
              split_space_nonl(String.drop(line,
                String.length(Cli.leading_indent(line))),
                drop_nonl(line,
                  String.length(Cli.leading_indent(line)), clean_2))))))

def wrap_lines_chunkgood(+cols: Nat, lines: List<&2, String>,
    clean: AllNoNL(lines)) ->
    ChunkGood(cols, Cli.wrap_lines(lines, cols)):
  match lines:
    case Nil{}: Unit{}
    case head <> tail:
      pair_elim(NoNL(head), AllNoNL(tail),
        ChunkGood(cols, Cli.wrap_lines(head <> tail, cols)), clean,
        eh => et => (wrap_line_all(cols, head, eh),
          wrap_lines_chunkgood(cols, tail, et)))

def p13_boolean_full(+cols: Nat, +s: String) ->
    {p13_bool(cols, String.lines(Cli.wrap(s, cols)))
      == True{} : Bool}:
  join_chunks_p13(cols, Cli.wrap_lines(String.lines(s), cols),
    wrap_lines_nonempty(String.lines(s), cols, split_nonempty(s, '\n')),
    wrap_lines_chunkgood(cols, String.lines(s), lines_all_nonl(s)))

def p13_alt_equiv(cols: Nat, xs: List<&2, String>) ->
    {List.all(~&2, ~Laws.P13Line, ~Laws.p13_entry_good,
      Laws.p13_lines(xs, cols)) == p13_bool(cols, xs) : Bool}:
  match xs:
    case Nil{}: {==}
    case head <> tail:
      Equal.cong(Bool, Bool,
        b => Bool.and(LineGood(cols, head), b),
        List.all(~&2, ~Laws.P13Line, ~Laws.p13_entry_good,
          Laws.p13_lines(tail, cols)),
        p13_bool(cols, tail), p13_alt_equiv(cols, tail))

def p13_alt_finish(+s: String, +cols: Nat) ->
    {List.all(~&2, ~Laws.P13Line, ~Laws.p13_entry_good,
      Laws.p13_lines(String.lines(Cli.wrap(s, cols)), cols))
      == True{} : Bool}:
  Equal.trans(Bool,
    List.all(~&2, ~Laws.P13Line, ~Laws.p13_entry_good,
      Laws.p13_lines(String.lines(Cli.wrap(s, cols)), cols)),
    p13_bool(cols, String.lines(Cli.wrap(s, cols))), True{},
    p13_alt_equiv(cols, String.lines(Cli.wrap(s, cols))),
    p13_boolean_full(cols, s))

def Laws.p13(s, cols):
  p13_alt_finish(s, cols)
