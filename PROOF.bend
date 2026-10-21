# Purpose: proofs of the pure CLI laws.
# Expected output: ALL PROOFS CHECK.
# Run: bend PROOF.bend --verdict

import Base
import ./cli.bend as Cli
import ./demo.bend as Demo
import ./LAWS.bend as Laws

def Laws.g_text_width():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.g_text_wrap():
  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))

def Laws.g_text_width_emoji():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==},
    ({==}, ({==}, {==}))))))))))))

def Laws.g_text_width_emoji_edges():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==},
    ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))))))))))

def Laws.g_text_wrap_emoji():
  ({==}, {==})

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

def Laws.g_lint_dup_global():
  {==}

def Laws.g_lint_dup_sub():
  {==}

def Laws.g_lint_reserved():
  {==}

def Laws.g_lint_reserved_sub():
  {==}

def Laws.g_lint_misplaced():
  {==}

def Laws.g_lint_required_sub():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))

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

def Laws.g_lint_bad_choice():
  ({==}, ({==}, ({==}, {==})))

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
    {String.starts_with.go.if("", t, b) == b : Bool}:
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

def plain_skip_free(s: String, +suffix: String,
    free: EscFree(s)) ->
    {Cli.strip_go(String.append(s, suffix), Cli.StripPlain{})
      == String.append(s, Cli.strip_go(suffix, Cli.StripPlain{})) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+head, +tail}:
      (free_head, free_tail) = free
      +rest = String.append(tail, suffix)
      +next = Cli.strip_go(rest, Cli.StripPlain{})
      step = Equal.cong(Bool, String,
        b => String.append(Bool.pick(String, b, "", Char.show(head)),
          Cli.strip_go(rest, Bool.pick(Cli.StripState, b,
            Cli.StripEsc{}, Cli.StripPlain{}))),
        Char.is_eq(head, '\u{1B}'), False{}, free_head)
      Equal.trans(String,
        Cli.strip_go(String.append(SCon{head, tail}, suffix),
          Cli.StripPlain{}),
        String.append(Char.show(head), next),
        String.append(SCon{head, tail},
          Cli.strip_go(suffix, Cli.StripPlain{})),
        step,
        Equal.cong(String, String,
          x => String.append(Char.show(head), x),
          next, String.append(tail,
            Cli.strip_go(suffix, Cli.StripPlain{})),
          plain_skip_free(tail, suffix, free_tail)))

def reset_skip(suffix: String) ->
    {Cli.strip_go(String.append("\u{1B}[0m", suffix), Cli.StripPlain{})
      == Cli.strip_go(suffix, Cli.StripPlain{}) : String}:
  {==}

def body_skip_tail(styles: List<&2, Cli.Style>, +suffix: String,
    pending: String) ->
    {Cli.strip_go(String.append(Cli.style_codes_tail(styles),
        String.append("m", suffix)), Cli.StripBody{pending})
      == Cli.strip_go(suffix, Cli.StripPlain{}) : String}:
  match styles:
    case Nil{}:
      {==}
    case head <> tail:
      match head:
        case Cli.Bold{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(pending, ";"), "1"))
        case Cli.Dim{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(pending, ";"), "2"))
        case Cli.Under{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(pending, ";"), "4"))
        case Cli.Red{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(String.append(pending, ";"), "3"), "1"))
        case Cli.Green{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(String.append(pending, ";"), "3"), "2"))
        case Cli.Yellow{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(String.append(pending, ";"), "3"), "3"))
        case Cli.Blue{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(String.append(pending, ";"), "3"), "4"))
        case Cli.Magenta{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(String.append(pending, ";"), "3"), "5"))
        case Cli.Cyan{}:
          body_skip_tail(tail, suffix,
            String.append(String.append(String.append(pending, ";"), "3"), "6"))

def body_skip_first(style: Cli.Style, tail: List<&2, Cli.Style>,
    +suffix: String, pending: String) ->
    {Cli.strip_go(String.append(String.append(Cli.style_code(style),
        Cli.style_codes_tail(tail)), String.append("m", suffix)),
      Cli.StripBody{pending})
      == Cli.strip_go(suffix, Cli.StripPlain{}) : String}:
  match style:
    case Cli.Bold{}:
      body_skip_tail(tail, suffix, String.append(pending, "1"))
    case Cli.Dim{}:
      body_skip_tail(tail, suffix, String.append(pending, "2"))
    case Cli.Under{}:
      body_skip_tail(tail, suffix, String.append(pending, "4"))
    case Cli.Red{}:
      body_skip_tail(tail, suffix,
        String.append(String.append(pending, "3"), "1"))
    case Cli.Green{}:
      body_skip_tail(tail, suffix,
        String.append(String.append(pending, "3"), "2"))
    case Cli.Yellow{}:
      body_skip_tail(tail, suffix,
        String.append(String.append(pending, "3"), "3"))
    case Cli.Blue{}:
      body_skip_tail(tail, suffix,
        String.append(String.append(pending, "3"), "4"))
    case Cli.Magenta{}:
      body_skip_tail(tail, suffix,
        String.append(String.append(pending, "3"), "5"))
    case Cli.Cyan{}:
      body_skip_tail(tail, suffix,
        String.append(String.append(pending, "3"), "6"))

def paint_skip_colored(+style: Cli.Style, +styles: List<&2, Cli.Style>,
    +source: String, +suffix: String, free: EscFree(source)) ->
    {Cli.strip_go(String.append(Cli.paint(True{}, style <> styles, source),
      suffix), Cli.StripPlain{})
      == String.append(source, Cli.strip_go(suffix, Cli.StripPlain{})) : String}:
  +codes = Cli.style_codes(style <> styles)
  +raw = String.append(Cli.paint(True{}, style <> styles, source), suffix)
  +after_reset = String.append("\u{1B}[0m", suffix)
  +after_text = String.append(source, after_reset)
  +shaped = String.append("\u{1B}[",
    String.append(codes, String.append("m", after_text)))
  step_shape = Equal.cong(String, String,
    x => Cli.strip_go(x, Cli.StripPlain{}), raw, shaped,
    paint_append_shape(codes, source, suffix))
  step_styles = body_skip_first(style, styles, after_text, "\u{1B}[")
  step_text = plain_skip_free(source, after_reset, free)
  step_reset = reset_skip(suffix)
  Equal.trans(String,
    Cli.strip_go(raw, Cli.StripPlain{}),
    Cli.strip_go(shaped, Cli.StripPlain{}),
    String.append(source, Cli.strip_go(suffix, Cli.StripPlain{})),
    step_shape,
    Equal.trans(String,
      Cli.strip_go(shaped, Cli.StripPlain{}),
      Cli.strip_go(after_text, Cli.StripPlain{}),
      String.append(source, Cli.strip_go(suffix, Cli.StripPlain{})),
      step_styles,
      Equal.trans(String,
        Cli.strip_go(after_text, Cli.StripPlain{}),
        String.append(source, Cli.strip_go(after_reset, Cli.StripPlain{})),
        String.append(source, Cli.strip_go(suffix, Cli.StripPlain{})),
        step_text,
        Equal.cong(String, String,
          x => String.append(source, x),
          Cli.strip_go(after_reset, Cli.StripPlain{}),
          Cli.strip_go(suffix, Cli.StripPlain{}), step_reset))))

def paint_skip(styles: List<&2, Cli.Style>, +source: String,
    +suffix: String, free: EscFree(source)) ->
    {Cli.strip_go(String.append(Cli.paint(True{}, styles, source), suffix),
      Cli.StripPlain{})
      == String.append(source, Cli.strip_go(suffix, Cli.StripPlain{})) : String}:
  match styles:
    case Nil{}:
      plain_skip_free(source, suffix, free)
    case head <> tail:
      paint_skip_colored(head, tail, source, suffix, free)

def emit_strip_free(segments: List<&2, Cli.Segment>,
    free: EscFree(Cli.emit(False{}, segments))) ->
    {Cli.strip_go(Cli.emit(True{}, segments), Cli.StripPlain{})
      == Cli.emit(False{}, segments) : String}:
  match segments:
    case Nil{}:
      {==}
    case Cli.Segment{+source, styles} <> +rest:
      +styled_tail = Cli.emit(True{}, rest)
      +plain_tail = Cli.emit(False{}, rest)
      pair_elim(EscFree(source), EscFree(plain_tail),
        {Cli.strip_go(String.append(Cli.paint(True{}, styles, source),
          styled_tail), Cli.StripPlain{})
          == String.append(source, plain_tail) : String},
        free_append_parts(source, plain_tail, free),
        source_free => rest_free =>
          Equal.trans(String,
            Cli.strip_go(String.append(Cli.paint(True{}, styles, source),
              styled_tail), Cli.StripPlain{}),
            String.append(source, Cli.strip_go(styled_tail,
              Cli.StripPlain{})),
            String.append(source, plain_tail),
            paint_skip(styles, source, styled_tail, source_free),
            Equal.cong(String, String,
              x => String.append(source, x),
              Cli.strip_go(styled_tail, Cli.StripPlain{}), plain_tail,
              emit_strip_free(rest, rest_free))))

def strip_no_esc(+s: String, free: EscFree(s)) ->
    {Cli.strip_go(s, Cli.StripPlain{}) == s : String}:
  Equal.trans(String,
    Cli.strip_go(s, Cli.StripPlain{}),
    Cli.strip_go(String.append(s, ""), Cli.StripPlain{}), s,
    Equal.cong(String, String,
      x => Cli.strip_go(x, Cli.StripPlain{}),
      s, String.append(s, ""),
      Equal.sym(String, String.append(s, ""), s, append_nil(s))),
    Equal.trans(String,
      Cli.strip_go(String.append(s, ""), Cli.StripPlain{}),
      String.append(s, Cli.strip_go("", Cli.StripPlain{})), s,
      plain_skip_free(s, "", free), append_nil(s)))

def paint_strip_no_esc(on: Bool, styles: List<&2, Cli.Style>, +s: String,
    free: EscFree(s)) ->
    {Cli.strip(Cli.paint(on, styles, s)) == s : String}:
  match on styles:
    case False{} _:
      strip_no_esc(s, free)
    case True{} Nil{}:
      strip_no_esc(s, free)
    case True{} +h <> +t:
      +painted = Cli.paint(True{}, h <> t, s)
      Equal.trans(String,
        Cli.strip_go(painted, Cli.StripPlain{}),
        Cli.strip_go(String.append(painted, ""), Cli.StripPlain{}),
        s,
        Equal.cong(String, String,
          x => Cli.strip_go(x, Cli.StripPlain{}), painted,
          String.append(painted, ""),
          Equal.sym(String, String.append(painted, ""), painted,
            append_nil(painted))),
        Equal.trans(String,
          Cli.strip_go(String.append(painted, ""), Cli.StripPlain{}),
          String.append(s, Cli.strip_go("", Cli.StripPlain{})), s,
          paint_skip(h <> t, s, "", free), append_nil(s)))

def Laws.p1(on, styles, s):
  ({==}, (prem => paint_strip_no_esc(on, styles, s,
    free_of_contains(s, prem))))

def Laws.p2(segments):
  prem => emit_strip_free(segments,
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

def join_safe_good(+cols: Nat, xs: List<&2, String>,
    non: NonEmpty(xs), safe: SafeLines(cols, xs)) ->
    AllGood(cols, String.lines(String.join(xs, "\n"))):
  match xs:
    case Nil{}:
      Empty.absurd(AllGood(cols, String.lines(String.join(Nil{}, "\n"))), non)
    case +head <> +tail:
      %Equal.sym(List<&2, String>,
        String.lines(String.join(head <> tail, "\n")),
        flatten_lines(head <> tail), join_lines_nonempty(head, tail))
        : AllGood(cols, _)
      safe_flatten_good(cols, head <> tail, safe)

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
      (empty_good(cols), Unit{})
    case True{}:
      join_safe_good(cols, List.reverse(&2, String, line <> done),
        reverse_nonempty(line, done),
        safe_reverse_go(cols, line <> done, Nil{},
          ((line_if, line_no), done_safe), Unit{}))

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

def p13_good_equiv(cols: Nat, xs: List<&2, String>) ->
    {Laws.p13_good(cols, xs) == p13_bool(cols, xs) : Bool}:
  match xs:
    case Nil{}: {==}
    case head <> tail:
      Equal.cong(Bool, Bool,
        b => Bool.and(LineGood(cols, head), b),
        Laws.p13_good(cols, tail), p13_bool(cols, tail),
        p13_good_equiv(cols, tail))

def p13_finish(+s: String, +cols: Nat) ->
    {Laws.p13_good(cols, String.lines(Cli.wrap(s, cols)))
      == True{} : Bool}:
  Equal.trans(Bool,
    Laws.p13_good(cols, String.lines(Cli.wrap(s, cols))),
    p13_bool(cols, String.lines(Cli.wrap(s, cols))), True{},
    p13_good_equiv(cols, String.lines(Cli.wrap(s, cols))),
    p13_boolean_full(cols, s))

def Laws.p13(s, cols):
  p13_finish(s, cols)

def list_append_assoc(+xs: List<&2, String>, +ys: List<&2, String>,
    +zs: List<&2, String>) ->
    {List.append(&2, String, List.append(&2, String, xs, ys), zs)
      == List.append(&2, String, xs, List.append(&2, String, ys, zs))
      : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case head <> tail:
      %list_append_assoc(tail, ys, zs) :
        {head <> List.append(&2, String,
          List.append(&2, String, tail, ys), zs) == head <> _
          : List<&2, String>}
      {==}

def all_words_append(xs: List<&2, String>, +ys: List<&2, String>) ->
    {Laws.all_words(List.append(&2, String, xs, ys))
      == List.append(&2, String, Laws.all_words(xs), Laws.all_words(ys))
      : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case +head <> +tail:
      Equal.trans(List<&2, String>,
        List.append(&2, String, Cli.words(head),
          Laws.all_words(List.append(&2, String, tail, ys))),
        List.append(&2, String, Cli.words(head),
          List.append(&2, String, Laws.all_words(tail),
            Laws.all_words(ys))),
        List.append(&2, String,
          List.append(&2, String, Cli.words(head), Laws.all_words(tail)),
          Laws.all_words(ys)),
        Equal.cong(List<&2, String>, List<&2, String>,
          rest => List.append(&2, String, Cli.words(head), rest),
          Laws.all_words(List.append(&2, String, tail, ys)),
          List.append(&2, String, Laws.all_words(tail),
            Laws.all_words(ys)), all_words_append(tail, ys)),
        Equal.sym(List<&2, String>,
          List.append(&2, String,
            List.append(&2, String, Cli.words(head), Laws.all_words(tail)),
            Laws.all_words(ys)),
          List.append(&2, String, Cli.words(head),
            List.append(&2, String, Laws.all_words(tail),
              Laws.all_words(ys))),
          list_append_assoc(Cli.words(head), Laws.all_words(tail),
            Laws.all_words(ys))))

def chunk_words(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}: Nil{}
    case head <> tail:
      List.append(&2, String, Laws.all_words(String.lines(head)),
        chunk_words(tail))

def all_words_flatten(xs: List<&2, String>) ->
    {Laws.all_words(flatten_lines(xs)) == chunk_words(xs)
      : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case +head <> +tail:
      Equal.trans(List<&2, String>,
        Laws.all_words(List.append(&2, String, String.lines(head),
          flatten_lines(tail))),
        List.append(&2, String,
          Laws.all_words(String.lines(head)),
          Laws.all_words(flatten_lines(tail))),
        chunk_words(head <> tail),
        all_words_append(String.lines(head), flatten_lines(tail)),
        Equal.cong(List<&2, String>, List<&2, String>,
          rest => List.append(&2, String,
            Laws.all_words(String.lines(head)), rest),
          Laws.all_words(flatten_lines(tail)), chunk_words(tail),
          all_words_flatten(tail)))

def join_words_nonempty(+head: String, +tail: List<&2, String>) ->
    {Laws.all_words(String.lines(String.join(head <> tail, "\n")))
      == chunk_words(head <> tail) : List<&2, String>}:
  Equal.trans(List<&2, String>,
    Laws.all_words(String.lines(String.join(head <> tail, "\n"))),
    Laws.all_words(flatten_lines(head <> tail)),
    chunk_words(head <> tail),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => Laws.all_words(xs),
      String.lines(String.join(head <> tail, "\n")),
      flatten_lines(head <> tail),
    join_lines_nonempty(head, tail)),
    all_words_flatten(head <> tail))

def split_append_space(s: String, +t: String) ->
    {String.split(String.append(s, String.append(" ", t)), ' ')
      == List.append(&2, String, String.split(s, ' '), String.split(t, ' '))
      : List<&2, String>}:
  match s:
    case SNil{}: {==}
    case SCon{+head, +tail}:
      Equal.trans(List<&2, String>,
        String.split.fin(head,
          String.split(String.append(tail, String.append(" ", t)), ' '),
          Char.is_eq(head, ' ')),
        String.split.fin(head,
          List.append(&2, String, String.split(tail, ' '),
            String.split(t, ' ')), Char.is_eq(head, ' ')),
        List.append(&2, String,
          String.split.fin(head, String.split(tail, ' '),
            Char.is_eq(head, ' ')), String.split(t, ' ')),
        Equal.cong(List<&2, String>, List<&2, String>,
          xs => String.split.fin(head, xs, Char.is_eq(head, ' ')),
          String.split(String.append(tail, String.append(" ", t)), ' '),
          List.append(&2, String, String.split(tail, ' '),
            String.split(t, ' ')), split_append_space(tail, t)),
        split_fin_append_nonempty(head, String.split(tail, ' '),
          String.split(t, ' '), Char.is_eq(head, ' '),
          split_nonempty(tail, ' ')))

def filter_put_append(head: String, xs: List<&2, String>,
    ys: List<&2, String>, keep: Bool) ->
    {List.filter.put(String, head, List.append(&2, String, xs, ys), keep)
      == List.append(&2, String, List.filter.put(String, head, xs, keep), ys)
      : List<&2, String>}:
  match keep:
    case False{}: {==}
    case True{}: {==}

def filter_words_append(xs: List<&2, String>, +ys: List<&2, String>) ->
    {List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
        List.append(&2, String, xs, ys))
      == List.append(&2, String,
        List.filter(~String, ~(w => Bool.not(String.is_empty(w))), xs),
        List.filter(~String, ~(w => Bool.not(String.is_empty(w))), ys))
      : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case +head <> +tail:
      Equal.trans(List<&2, String>,
        List.filter.put(String, head,
          List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
            List.append(&2, String, tail, ys)),
          Bool.not(String.is_empty(head))),
        List.filter.put(String, head,
          List.append(&2, String,
            List.filter(~String, ~(w => Bool.not(String.is_empty(w))), tail),
            List.filter(~String, ~(w => Bool.not(String.is_empty(w))), ys)),
          Bool.not(String.is_empty(head))),
        List.append(&2, String,
          List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
            head <> tail),
          List.filter(~String, ~(w => Bool.not(String.is_empty(w))), ys)),
        Equal.cong(List<&2, String>, List<&2, String>,
          zs => List.filter.put(String, head, zs,
            Bool.not(String.is_empty(head))),
          List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
            List.append(&2, String, tail, ys)),
          List.append(&2, String,
            List.filter(~String, ~(w => Bool.not(String.is_empty(w))), tail),
            List.filter(~String, ~(w => Bool.not(String.is_empty(w))), ys)),
          filter_words_append(tail, ys)),
        filter_put_append(head,
          List.filter(~String, ~(w => Bool.not(String.is_empty(w))), tail),
          List.filter(~String, ~(w => Bool.not(String.is_empty(w))), ys),
          Bool.not(String.is_empty(head))))

def words_append_space(+a: String, +b: String) ->
    {Cli.words(String.append(a, String.append(" ", b)))
      == List.append(&2, String, Cli.words(a), Cli.words(b))
      : List<&2, String>}:
  Equal.trans(List<&2, String>,
    Cli.words(String.append(a, String.append(" ", b))),
    List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
      List.append(&2, String, String.split(a, ' '), String.split(b, ' '))),
    List.append(&2, String, Cli.words(a), Cli.words(b)),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => List.filter(~String, ~(w => Bool.not(String.is_empty(w))), xs),
      String.split(String.append(a, String.append(" ", b)), ' '),
      List.append(&2, String, String.split(a, ' '), String.split(b, ' ')),
      split_append_space(a, b)),
    filter_words_append(String.split(a, ' '), String.split(b, ' ')))

def words_spaced_prefix(+indent: String, +s: String,
    spaces: Spaces(indent)) ->
    {Cli.words(String.append(indent, s)) == Cli.words(s)
      : List<&2, String>}:
  match indent:
    case SNil{}: {==}
    case SCon{+head, +tail}:
      pair_elim({Char.is_eq(head, ' ') == True{} : Bool}, Spaces(tail),
        {Cli.words(String.append(SCon{head, tail}, s)) == Cli.words(s)
          : List<&2, String>}, spaces,
        eh => et =>
          Equal.trans(List<&2, String>,
            Cli.words(String.append(SCon{head, tail}, s)),
            Cli.words(String.append(tail, s)), Cli.words(s),
            Equal.cong(Bool, List<&2, String>,
              cut => List.filter(~String,
                ~(w => Bool.not(String.is_empty(w))),
                String.split.fin(head,
                  String.split(String.append(tail, s), ' '), cut)),
              Char.is_eq(head, ' '), True{}, eh),
            words_spaced_prefix(tail, s, et)))

def words_single(+s: String, clean: NoSpace(s),
    non: {String.is_empty(s) == False{} : Bool}) ->
    {Cli.words(s) == [s] : List<&2, String>}:
  Equal.trans(List<&2, String>, Cli.words(s),
    List.filter(~String, ~(w => Bool.not(String.is_empty(w))), [s]),
    [s],
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => List.filter(~String, ~(w => Bool.not(String.is_empty(w))), xs),
      String.split(s, ' '), [s], split_nospace(s, clean)),
    Equal.cong(Bool, List<&2, String>,
      b => List.filter.put(String, s, Nil{}, Bool.not(b)),
      String.is_empty(s), False{}, non))

def reverse_go_append(xs: List<&2, String>, +ys: List<&2, String>,
    +zs: List<&2, String>) ->
    {List.reverse.go(&2, String, xs,
        List.append(&2, String, ys, zs))
      == List.append(&2, String,
        List.reverse.go(&2, String, xs, ys), zs)
      : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case head <> tail:
      reverse_go_append(tail, head <> ys, zs)

def reverse_cons(+head: String, +tail: List<&2, String>) ->
    {List.reverse(&2, String, head <> tail)
      == List.append(&2, String, List.reverse(&2, String, tail), [head])
      : List<&2, String>}:
  reverse_go_append(tail, Nil{}, [head])

def chunk_words_append(xs: List<&2, String>, +ys: List<&2, String>) ->
    {chunk_words(List.append(&2, String, xs, ys))
      == List.append(&2, String, chunk_words(xs), chunk_words(ys))
      : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case +head <> +tail:
      Equal.trans(List<&2, String>,
        List.append(&2, String, Laws.all_words(String.lines(head)),
          chunk_words(List.append(&2, String, tail, ys))),
        List.append(&2, String, Laws.all_words(String.lines(head)),
          List.append(&2, String, chunk_words(tail), chunk_words(ys))),
        List.append(&2, String,
          List.append(&2, String, Laws.all_words(String.lines(head)),
            chunk_words(tail)), chunk_words(ys)),
        Equal.cong(List<&2, String>, List<&2, String>,
          rest => List.append(&2, String,
            Laws.all_words(String.lines(head)), rest),
          chunk_words(List.append(&2, String, tail, ys)),
          List.append(&2, String, chunk_words(tail), chunk_words(ys)),
          chunk_words_append(tail, ys)),
        Equal.sym(List<&2, String>,
          List.append(&2, String,
            List.append(&2, String, Laws.all_words(String.lines(head)),
              chunk_words(tail)), chunk_words(ys)),
          List.append(&2, String, Laws.all_words(String.lines(head)),
            List.append(&2, String, chunk_words(tail), chunk_words(ys))),
          list_append_assoc(Laws.all_words(String.lines(head)),
            chunk_words(tail), chunk_words(ys))))

def rev_chunk_step(+line: String, +done: List<&2, String>) ->
    {chunk_words(List.reverse(&2, String, line <> done))
      == List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)),
        Laws.all_words(String.lines(line)))
      : List<&2, String>}:
  Equal.trans(List<&2, String>,
    chunk_words(List.reverse(&2, String, line <> done)),
    chunk_words(List.append(&2, String,
      List.reverse(&2, String, done), [line])),
    List.append(&2, String,
      chunk_words(List.reverse(&2, String, done)),
      Laws.all_words(String.lines(line))),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => chunk_words(xs),
      List.reverse(&2, String, line <> done),
      List.append(&2, String, List.reverse(&2, String, done), [line]),
      reverse_cons(line, done)),
    Equal.trans(List<&2, String>,
      chunk_words(List.append(&2, String,
        List.reverse(&2, String, done), [line])),
      List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)),
        List.append(&2, String, Laws.all_words(String.lines(line)), Nil{})),
      List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)),
        Laws.all_words(String.lines(line))),
      chunk_words_append(List.reverse(&2, String, done), [line]),
      Equal.cong(List<&2, String>, List<&2, String>,
        xs => List.append(&2, String,
          chunk_words(List.reverse(&2, String, done)), xs),
        List.append(&2, String, Laws.all_words(String.lines(line)), Nil{}),
        Laws.all_words(String.lines(line)),
        list_append_nil(Laws.all_words(String.lines(line))))))

def all_words_single(+line: String, clean: NoNL(line)) ->
    {Laws.all_words(String.lines(line)) == Cli.words(line)
      : List<&2, String>}:
  Equal.trans(List<&2, String>,
    Laws.all_words(String.lines(line)), Laws.all_words([line]),
    Cli.words(line),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => Laws.all_words(xs), String.lines(line), [line],
      lines_nolf(line, clean)),
    list_append_nil(Cli.words(line)))

def rev_chunk_clean(+line: String, +done: List<&2, String>,
    clean: NoNL(line)) ->
    {chunk_words(List.reverse(&2, String, line <> done))
      == List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)), Cli.words(line))
      : List<&2, String>}:
  Equal.trans(List<&2, String>,
    chunk_words(List.reverse(&2, String, line <> done)),
    List.append(&2, String,
      chunk_words(List.reverse(&2, String, done)),
      Laws.all_words(String.lines(line))),
    List.append(&2, String,
      chunk_words(List.reverse(&2, String, done)), Cli.words(line)),
    rev_chunk_step(line, done),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)), xs),
      Laws.all_words(String.lines(line)), Cli.words(line),
      all_words_single(line, clean)))

def AllNonEmpty(xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}: Unit
    case head <> tail:
      {String.is_empty(head) == False{} : Bool} & AllNonEmpty(tail)

def filter_all_nonempty(xs: List<&2, String>) ->
    AllNonEmpty(List.filter(~String,
      ~(w => Bool.not(String.is_empty(w))), xs)):
  match xs:
    case Nil{}: Unit{}
    case head <> tail:
      match head:
        case SNil{}:
          filter_all_nonempty(tail)
        case SCon{head, rest}:
          ({==}, filter_all_nonempty(tail))

def list_append_one(+xs: List<&2, String>, +word: String,
    +rest: List<&2, String>) ->
    {List.append(&2, String,
        List.append(&2, String, xs, [word]), rest)
      == List.append(&2, String, xs, word <> rest)
      : List<&2, String>}:
  list_append_assoc(xs, [word], rest)

def WrapGoalWords(words: List<&2, String>, indent: String, cols: Nat,
    line: String, done: List<&2, String>) -> Type:
  {Laws.all_words(String.lines(Cli.wrap_words(words,
      Cli.WrapState{indent, cols, line, True{}, done})))
    == List.append(&2, String,
      chunk_words(List.reverse(&2, String, done)),
      List.append(&2, String, Cli.words(line), words))
    : List<&2, String>}

def join_words_any(xs: List<&2, String>, non: NonEmpty(xs)) ->
    {Laws.all_words(String.lines(String.join(xs, "\n")))
      == chunk_words(xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      Empty.absurd({Laws.all_words(String.lines(String.join(Nil{}, "\n")))
        == chunk_words(Nil{}) : List<&2, String>}, non)
    case head <> tail:
      join_words_nonempty(head, tail)

def wrap_words_base_preserve(+indent: String, +cols: Nat,
    +line: String, +done: List<&2, String>, clean: NoNL(line)) ->
    WrapGoalWords(Nil{}, indent, cols, line, done):
  Equal.trans(List<&2, String>,
    Laws.all_words(String.lines(String.join(
      List.reverse(&2, String, line <> done), "\n"))),
    chunk_words(List.reverse(&2, String, line <> done)),
    List.append(&2, String,
      chunk_words(List.reverse(&2, String, done)),
      List.append(&2, String, Cli.words(line), Nil{})),
    join_words_any(List.reverse(&2, String, line <> done),
      reverse_nonempty(line, done)),
    Equal.trans(List<&2, String>,
      chunk_words(List.reverse(&2, String, line <> done)),
      List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)), Cli.words(line)),
      List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)),
        List.append(&2, String, Cli.words(line), Nil{})),
      rev_chunk_clean(line, done, clean),
      Equal.cong(List<&2, String>, List<&2, String>,
        xs => List.append(&2, String,
          chunk_words(List.reverse(&2, String, done)), xs),
        Cli.words(line), List.append(&2, String, Cli.words(line), Nil{}),
        Equal.sym(List<&2, String>,
          List.append(&2, String, Cli.words(line), Nil{}),
          Cli.words(line), list_append_nil(Cli.words(line))))))

def words_candidate(+line: String, +word: String,
    clean: NoSpace(word), non: {String.is_empty(word) == False{} : Bool}) ->
    {Cli.words(String.append(line, String.append(" ", word)))
      == List.append(&2, String, Cli.words(line), [word])
      : List<&2, String>}:
  Equal.trans(List<&2, String>,
    Cli.words(String.append(line, String.append(" ", word))),
    List.append(&2, String, Cli.words(line), Cli.words(word)),
    List.append(&2, String, Cli.words(line), [word]),
    words_append_space(line, word),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => List.append(&2, String, Cli.words(line), xs),
      Cli.words(word), [word], words_single(word, clean, non)))

def fit_words_target(+line: String, +word: String,
    +rest: List<&2, String>, +rev: List<&2, String>,
    clean: NoSpace(word), non: {String.is_empty(word) == False{} : Bool}) ->
    {List.append(&2, String, rev,
        List.append(&2, String,
          Cli.words(String.append(line, String.append(" ", word))), rest))
      == List.append(&2, String, rev,
        List.append(&2, String, Cli.words(line), word <> rest))
      : List<&2, String>}:
  Equal.trans(List<&2, String>,
    List.append(&2, String, rev,
      List.append(&2, String,
        Cli.words(String.append(line, String.append(" ", word))), rest)),
    List.append(&2, String, rev,
      List.append(&2, String,
        List.append(&2, String, Cli.words(line), [word]), rest)),
    List.append(&2, String, rev,
      List.append(&2, String, Cli.words(line), word <> rest)),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => List.append(&2, String, rev,
        List.append(&2, String, xs, rest)),
      Cli.words(String.append(line, String.append(" ", word))),
      List.append(&2, String, Cli.words(line), [word]),
      words_candidate(line, word, clean, non)),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => List.append(&2, String, rev, xs),
      List.append(&2, String,
        List.append(&2, String, Cli.words(line), [word]), rest),
      List.append(&2, String, Cli.words(line), word <> rest),
      list_append_one(Cli.words(line), word, rest)))

def words_indent_word(+indent: String, +word: String,
    spaces: Spaces(indent), clean: NoSpace(word),
    non: {String.is_empty(word) == False{} : Bool}) ->
    {Cli.words(String.append(indent, word)) == [word]
      : List<&2, String>}:
  Equal.trans(List<&2, String>,
    Cli.words(String.append(indent, word)), Cli.words(word), [word],
    words_spaced_prefix(indent, word, spaces),
    words_single(word, clean, non))

def break_words_target(+line: String, +done: List<&2, String>,
    +indent: String, +word: String, +rest: List<&2, String>,
    line_no: NoNL(line), spaces: Spaces(indent),
    clean: NoSpace(word), non: {String.is_empty(word) == False{} : Bool}) ->
    {List.append(&2, String,
        chunk_words(List.reverse(&2, String, line <> done)),
        List.append(&2, String,
          Cli.words(String.append(indent, word)), rest))
      == List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)),
        List.append(&2, String, Cli.words(line), word <> rest))
      : List<&2, String>}:
  Equal.trans(List<&2, String>,
    List.append(&2, String,
      chunk_words(List.reverse(&2, String, line <> done)),
      List.append(&2, String, Cli.words(String.append(indent, word)), rest)),
    List.append(&2, String,
      List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)), Cli.words(line)),
      List.append(&2, String,
        Cli.words(String.append(indent, word)), rest)),
    List.append(&2, String,
      chunk_words(List.reverse(&2, String, done)),
      List.append(&2, String, Cli.words(line), word <> rest)),
    Equal.cong(List<&2, String>, List<&2, String>,
      xs => List.append(&2, String, xs,
        List.append(&2, String,
          Cli.words(String.append(indent, word)), rest)),
      chunk_words(List.reverse(&2, String, line <> done)),
      List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)), Cli.words(line)),
      rev_chunk_clean(line, done, line_no)),
    Equal.trans(List<&2, String>,
      List.append(&2, String,
        List.append(&2, String,
          chunk_words(List.reverse(&2, String, done)), Cli.words(line)),
        List.append(&2, String,
          Cli.words(String.append(indent, word)), rest)),
      List.append(&2, String,
        List.append(&2, String,
          chunk_words(List.reverse(&2, String, done)), Cli.words(line)),
        word <> rest),
      List.append(&2, String,
        chunk_words(List.reverse(&2, String, done)),
        List.append(&2, String, Cli.words(line), word <> rest)),
      Equal.cong(List<&2, String>, List<&2, String>,
        xs => List.append(&2, String,
          List.append(&2, String,
            chunk_words(List.reverse(&2, String, done)), Cli.words(line)),
          List.append(&2, String, xs, rest)),
        Cli.words(String.append(indent, word)), [word],
        words_indent_word(indent, word, spaces, clean, non)),
      list_append_assoc(
        chunk_words(List.reverse(&2, String, done)),
        Cli.words(line), word <> rest)))

def WrapRecWords(+rest: List<&2, String>, +indent: String,
    +cols: Nat) -> Type:
  @next_line:String -> @next_done:List<&2, String> ->
    Spaces(indent) -> NoNL(indent) -> NoNL(next_line) ->
    WrapGoalWords(rest, indent, cols, next_line, next_done)

def wrap_words_true_preserve(+word: String, +rest: List<&2, String>,
    +indent: String, +cols: Nat, +line: String,
    +done: List<&2, String>, fit: Bool,
    eq: {fit == Nat.is_le(Cli.width(Cli.strip(
      String.append(line, String.append(" ", word)))), cols) : Bool},
    spaces: Spaces(indent), indent_no: NoNL(indent),
    line_no: NoNL(line), clean: NoSpace(word),
    word_no: NoNL(word), non: {String.is_empty(word) == False{} : Bool},
    rec: WrapRecWords(rest, indent, cols)) ->
    WrapGoalWords(word <> rest, indent, cols, line, done):
  match fit:
    case True{}:
      Equal.trans(List<&2, String>,
        Laws.all_words(String.lines(Cli.wrap_words(word <> rest,
          Cli.WrapState{indent, cols, line, True{}, done}))),
        Laws.all_words(String.lines(Cli.wrap_words(rest,
          Cli.WrapState{indent, cols,
            String.append(line, String.append(" ", word)), True{}, done}))),
        List.append(&2, String,
          chunk_words(List.reverse(&2, String, done)),
          List.append(&2, String, Cli.words(line), word <> rest)),
        Equal.cong(Bool, List<&2, String>,
          cut => Laws.all_words(String.lines(Cli.wrap_words(rest,
            Bool.pick(Cli.WrapState, cut,
              Cli.WrapState{indent, cols,
                String.append(line, String.append(" ", word)), True{}, done},
              Cli.WrapState{indent, cols, String.append(indent, word),
                True{}, line <> done})))),
          Nat.is_le(Cli.width(Cli.strip(
            String.append(line, String.append(" ", word)))), cols),
          True{}, Equal.sym(Bool, True{},
            Nat.is_le(Cli.width(Cli.strip(
              String.append(line, String.append(" ", word)))), cols), eq)),
        Equal.trans(List<&2, String>,
          Laws.all_words(String.lines(Cli.wrap_words(rest,
            Cli.WrapState{indent, cols,
              String.append(line, String.append(" ", word)), True{}, done}))),
          List.append(&2, String,
            chunk_words(List.reverse(&2, String, done)),
            List.append(&2, String,
              Cli.words(String.append(line, String.append(" ", word))), rest)),
          List.append(&2, String,
            chunk_words(List.reverse(&2, String, done)),
            List.append(&2, String, Cli.words(line), word <> rest)),
          rec(String.append(line, String.append(" ", word)))(done)(spaces)(
            indent_no)(append_nonl(line, String.append(" ", word), line_no,
              append_nonl(" ", word, ({==}, Unit{}), word_no))),
          fit_words_target(line, word, rest,
            chunk_words(List.reverse(&2, String, done)), clean, non)))
    case False{}:
      pair_elim(Spaces(indent), Spaces(indent),
        WrapGoalWords(word <> rest, indent, cols, line, done),
        copy_spaces(indent, spaces), spaces_1 => spaces_2 =>
          pair_elim(NoNL(indent), NoNL(indent),
            WrapGoalWords(word <> rest, indent, cols, line, done),
            copy_nonl(indent, indent_no), indent_no_1 => indent_no_2 =>
              Equal.trans(List<&2, String>,
                Laws.all_words(String.lines(Cli.wrap_words(word <> rest,
                  Cli.WrapState{indent, cols, line, True{}, done}))),
                Laws.all_words(String.lines(Cli.wrap_words(rest,
                  Cli.WrapState{indent, cols, String.append(indent, word),
                    True{}, line <> done}))),
                List.append(&2, String,
                  chunk_words(List.reverse(&2, String, done)),
                  List.append(&2, String, Cli.words(line), word <> rest)),
                Equal.cong(Bool, List<&2, String>,
                  cut => Laws.all_words(String.lines(Cli.wrap_words(rest,
                    Bool.pick(Cli.WrapState, cut,
                      Cli.WrapState{indent, cols,
                        String.append(line, String.append(" ", word)),
                        True{}, done},
                      Cli.WrapState{indent, cols,
                        String.append(indent, word), True{}, line <> done})))),
                  Nat.is_le(Cli.width(Cli.strip(
                    String.append(line, String.append(" ", word)))), cols),
                  False{}, Equal.sym(Bool, False{},
                    Nat.is_le(Cli.width(Cli.strip(
                      String.append(line, String.append(" ", word)))), cols),
                    eq)),
                Equal.trans(List<&2, String>,
                  Laws.all_words(String.lines(Cli.wrap_words(rest,
                    Cli.WrapState{indent, cols,
                      String.append(indent, word), True{}, line <> done}))),
                  List.append(&2, String,
                    chunk_words(List.reverse(&2, String, line <> done)),
                    List.append(&2, String,
                      Cli.words(String.append(indent, word)), rest)),
                  List.append(&2, String,
                    chunk_words(List.reverse(&2, String, done)),
                    List.append(&2, String, Cli.words(line), word <> rest)),
                  rec(String.append(indent, word))(line <> done)(spaces_1)(
                    indent_no_1)(append_nonl(indent, word,
                      indent_no_2, word_no)),
                  break_words_target(line, done, indent, word, rest,
                    line_no, spaces_2, clean, non)))))

def wrap_words_preserve(words: List<&2, String>, +indent: String,
    +cols: Nat, +line: String, +done: List<&2, String>,
    spaces: Spaces(indent), indent_no: NoNL(indent),
    line_no: NoNL(line), clean: AllNoSpace(words),
    nonl: AllNoNL(words), nonempty: AllNonEmpty(words)) ->
    WrapGoalWords(words, indent, cols, line, done):
  match words:
    case Nil{}:
      wrap_words_base_preserve(indent, cols, line, done, line_no)
    case +word <> +rest:
      (word_clean, rest_clean) = clean
      (word_no, rest_no) = nonl
      (word_non, rest_non) = nonempty
      wrap_words_true_preserve(word, rest, indent, cols, line, done,
        Nat.is_le(Cli.width(Cli.strip(
          String.append(line, String.append(" ", word)))), cols), {==},
        spaces, indent_no, line_no, word_clean, word_no, word_non,
        next_line => next_done => next_spaces => next_indent_no =>
          next_line_no =>
            wrap_words_preserve(rest, indent, cols, next_line, next_done,
              next_spaces, next_indent_no, next_line_no,
              rest_clean, rest_no, rest_non))

def wrap_words_initial(words: List<&2, String>, +indent: String,
    +cols: Nat, spaces: Spaces(indent), indent_no: NoNL(indent),
    clean: AllNoSpace(words), nonl: AllNoNL(words),
    nonempty: AllNonEmpty(words)) ->
    {Laws.all_words(String.lines(Cli.wrap_words(words,
      Cli.WrapState{indent, cols, indent, False{}, Nil{}})))
      == words : List<&2, String>}:
  match words:
    case Nil{}:
      {==}
    case +word <> +rest:
      (word_clean, rest_clean) = clean
      (word_no, rest_no) = nonl
      (word_non, rest_non) = nonempty
      pair_elim(Spaces(indent), Spaces(indent),
        {Laws.all_words(String.lines(Cli.wrap_words(word <> rest,
          Cli.WrapState{indent, cols, indent, False{}, Nil{}})))
          == word <> rest : List<&2, String>},
        copy_spaces(indent, spaces), spaces_1 => spaces_2 =>
          pair_elim(NoNL(indent), NoNL(indent),
            {Laws.all_words(String.lines(Cli.wrap_words(word <> rest,
              Cli.WrapState{indent, cols, indent, False{}, Nil{}})))
              == word <> rest : List<&2, String>},
            copy_nonl(indent, indent_no), indent_no_1 => indent_no_2 =>
              Equal.trans(List<&2, String>,
                Laws.all_words(String.lines(Cli.wrap_words(word <> rest,
                  Cli.WrapState{indent, cols, indent, False{}, Nil{}}))),
                List.append(&2, String,
                  Cli.words(String.append(indent, word)), rest),
                word <> rest,
                wrap_words_preserve(rest, indent, cols,
                  String.append(indent, word), Nil{}, spaces_1,
                  indent_no_1, append_nonl(indent, word,
                    indent_no_2, word_no), rest_clean, rest_no, rest_non),
                Equal.cong(List<&2, String>, List<&2, String>,
                  xs => List.append(&2, String, xs, rest),
                  Cli.words(String.append(indent, word)), [word],
                  words_indent_word(indent, word,
                    spaces_2, word_clean, word_non)))))

def words_space_head(+head: Char, +tail: String,
    space: {Char.is_eq(head, ' ') == True{} : Bool}) ->
    {Cli.words(SCon{head, tail}) == Cli.words(tail)
      : List<&2, String>}:
  Equal.cong(Bool, List<&2, String>,
    cut => List.filter(~String,
      ~(w => Bool.not(String.is_empty(w))),
      String.split.fin(head, String.split(tail, ' '), cut)),
    Char.is_eq(head, ' '), True{}, space)

def words_drop_indent_fin(+head: Char, +tail: String, cut: Bool,
    +eq: {cut == Char.is_eq(head, ' ') : Bool},
    rec: {Cli.words(tail) == Cli.words(String.drop(tail,
      String.length(Cli.leading_indent(tail)))) : List<&2, String>}) ->
    {Cli.words(SCon{head, tail})
      == Cli.words(String.drop(SCon{head, tail},
        String.length(Cli.leading_indent(SCon{head, tail}))))
      : List<&2, String>}:
  match cut:
    case False{}:
      Equal.sym(List<&2, String>,
        Cli.words(String.drop(SCon{head, tail},
          String.length(Cli.leading_indent(SCon{head, tail})))),
        Cli.words(SCon{head, tail}),
        Equal.cong(Bool, List<&2, String>,
          b => Cli.words(String.drop(SCon{head, tail},
            String.length(Bool.pick(String, b,
              SCon{head, Cli.leading_indent(tail)}, "")))),
          Char.is_eq(head, ' '), False{},
          Equal.sym(Bool, False{}, Char.is_eq(head, ' '), eq)))
    case True{}:
      Equal.trans(List<&2, String>,
        Cli.words(SCon{head, tail}), Cli.words(tail),
        Cli.words(String.drop(SCon{head, tail},
          String.length(Cli.leading_indent(SCon{head, tail})))),
        words_space_head(head, tail,
          Equal.sym(Bool, True{}, Char.is_eq(head, ' '), eq)),
        Equal.trans(List<&2, String>,
          Cli.words(tail), Cli.words(String.drop(tail,
            String.length(Cli.leading_indent(tail)))),
          Cli.words(String.drop(SCon{head, tail},
            String.length(Cli.leading_indent(SCon{head, tail})))),
          rec,
          Equal.sym(List<&2, String>,
            Cli.words(String.drop(SCon{head, tail},
              String.length(Cli.leading_indent(SCon{head, tail})))),
            Cli.words(String.drop(tail,
              String.length(Cli.leading_indent(tail)))),
            Equal.cong(Bool, List<&2, String>,
              b => Cli.words(String.drop(SCon{head, tail},
                String.length(Bool.pick(String, b,
                  SCon{head, Cli.leading_indent(tail)}, "")))),
              Char.is_eq(head, ' '), True{},
              Equal.sym(Bool, True{}, Char.is_eq(head, ' '), eq)))))

def words_drop_indent(line: String) ->
    {Cli.words(line) == Cli.words(String.drop(line,
      String.length(Cli.leading_indent(line))))
      : List<&2, String>}:
  match line:
    case SNil{}: {==}
    case SCon{+head, +tail}:
      words_drop_indent_fin(head, tail, Char.is_eq(head, ' '), {==},
        words_drop_indent(tail))

def wrap_line_words(+line: String, +cols: Nat,
    clean: NoNL(line)) ->
    {Laws.all_words(String.lines(Cli.wrap_line(line, cols)))
      == Cli.words(line) : List<&2, String>}:
  pair_elim(NoNL(line), NoNL(line),
    {Laws.all_words(String.lines(Cli.wrap_line(line, cols)))
      == Cli.words(line) : List<&2, String>},
    copy_nonl(line, clean), line_no_1 => line_no_2 =>
      Equal.trans(List<&2, String>,
        Laws.all_words(String.lines(Cli.wrap_line(line, cols))),
        Cli.words(String.drop(line,
          String.length(Cli.leading_indent(line)))),
        Cli.words(line),
        wrap_words_initial(
          Cli.words(String.drop(line,
            String.length(Cli.leading_indent(line)))),
          Cli.leading_indent(line), cols, indent_spaces(line),
          indent_nonl(line, line_no_1),
          filter_all_nospace(String.split(String.drop(line,
            String.length(Cli.leading_indent(line))), ' '),
            split_all_nospace(String.drop(line,
              String.length(Cli.leading_indent(line))))),
          filter_all_nonl(String.split(String.drop(line,
            String.length(Cli.leading_indent(line))), ' '),
            split_space_nonl(String.drop(line,
              String.length(Cli.leading_indent(line))),
              drop_nonl(line, String.length(Cli.leading_indent(line)),
                line_no_2))),
          filter_all_nonempty(String.split(String.drop(line,
            String.length(Cli.leading_indent(line))), ' '))),
        Equal.sym(List<&2, String>,
          Cli.words(line),
          Cli.words(String.drop(line,
            String.length(Cli.leading_indent(line)))),
          words_drop_indent(line))))

def wrap_lines_words(lines: List<&2, String>, +cols: Nat,
    clean: AllNoNL(lines)) ->
    {chunk_words(Cli.wrap_lines(lines, cols))
      == Laws.all_words(lines) : List<&2, String>}:
  match lines:
    case Nil{}: {==}
    case +head <> +tail:
      pair_elim(NoNL(head), AllNoNL(tail),
        {chunk_words(Cli.wrap_lines(head <> tail, cols))
          == Laws.all_words(head <> tail) : List<&2, String>},
        clean, head_no => tail_no =>
          Equal.trans(List<&2, String>,
            chunk_words(Cli.wrap_lines(head <> tail, cols)),
            List.append(&2, String, Cli.words(head),
              chunk_words(Cli.wrap_lines(tail, cols))),
            Laws.all_words(head <> tail),
            Equal.cong(List<&2, String>, List<&2, String>,
              xs => List.append(&2, String, xs,
                chunk_words(Cli.wrap_lines(tail, cols))),
              Laws.all_words(String.lines(Cli.wrap_line(head, cols))),
              Cli.words(head), wrap_line_words(head, cols, head_no)),
            Equal.cong(List<&2, String>, List<&2, String>,
              xs => List.append(&2, String, Cli.words(head), xs),
              chunk_words(Cli.wrap_lines(tail, cols)),
              Laws.all_words(tail),
              wrap_lines_words(tail, cols, tail_no))))

def p14_finish(+s: String, +cols: Nat) ->
    {Laws.all_words(String.lines(Cli.wrap(s, cols)))
      == Laws.all_words(String.lines(s)) : List<&2, String>}:
  Equal.trans(List<&2, String>,
    Laws.all_words(String.lines(Cli.wrap(s, cols))),
    chunk_words(Cli.wrap_lines(String.lines(s), cols)),
    Laws.all_words(String.lines(s)),
    join_words_any(Cli.wrap_lines(String.lines(s), cols),
      wrap_lines_nonempty(String.lines(s), cols,
        split_nonempty(s, '\n'))),
    wrap_lines_words(String.lines(s), cols, lines_all_nonl(s)))

def Laws.p14(s, cols):
  p14_finish(s, cols)

def false_true_absurd(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_disc(Bool.not(_))
  Unit{}

def bool_cmp_refl(b: Bool) -> {EQ{} == Bool.cmp(b, b) : Cmp}:
  match b:
    case True{}: {==}
    case False{}: {==}

def word_cmp_refl(n: Nat, w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          %word_cmp_refl(p, t) : {EQ{} == Word.cmp.fin(b, b, _) : Cmp}
          bool_cmp_refl(b)

def string_order_refl(s: String) ->
    {EQ{} == String.order.go(s, s, EQ{}) : Cmp}:
  match s:
    case SNil{}: {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          match x:
            case U32{w}:
              %word_cmp_refl(32n, w) :
                {EQ{} == String.order.go(t, t, _) : Cmp}
              string_order_refl(t)

def string_eq_refl(s: String) -> {String.eq(s, s) == True{} : Bool}:
  %string_order_refl(s) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def same_take_prefix(xs: List<&2, String>, +ys: List<&2, String>) ->
    {Laws.same_strings(xs, List.take(&2, String,
      List.append(&2, String, xs, ys), List.length(&2, String, xs)))
      == True{} : Bool}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}: {==}
        case y <> yt: {==}
    case +x <> +xt:
      and_true(String.eq(x, x),
        Laws.same_strings(xt, List.take(&2, String,
          List.append(&2, String, xt, ys), List.length(&2, String, xt))),
        string_eq_refl(x), same_take_prefix(xt, ys))

def same_take_reverse(xs: List<&2, String>, acc: List<&2, String>,
    ys: List<&2, String>) ->
    {Laws.same_strings(List.reverse.go(&2, String, xs, acc),
      List.take(&2, String,
        List.reverse.go(&2, String, xs, List.append(&2, String, acc, ys)),
        List.length(&2, String, List.reverse.go(&2, String, xs, acc))))
      == True{} : Bool}:
  match xs:
    case Nil{}: same_take_prefix(acc, ys)
    case x <> xt: same_take_reverse(xt, x <> acc, ys)

def add_succ_right(n: Nat, m: Nat) ->
    {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n: {==}
    case 1n+p:
      %add_succ_right(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def add_zero_right(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n: {==}
    case 1n+p:
      %add_zero_right(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def length_reverse_go(xs: List<&2, String>, +acc: List<&2, String>) ->
    {List.length(&2, String, List.reverse.go(&2, String, xs, acc))
      == Nat.add(List.length(&2, String, xs), List.length(&2, String, acc))
      : Nat}:
  match xs:
    case Nil{}: {==}
    case x <> +xt:
      %add_succ_right(List.length(&2, String, xt),
        List.length(&2, String, acc)) :
        {List.length(&2, String, List.reverse.go(&2, String, xt, x <> acc))
          == _ : Nat}
      length_reverse_go(xt, x <> acc)

def length_reverse(+xs: List<&2, String>) ->
    {List.length(&2, String, List.reverse.go(&2, String, xs, Nil{}))
      == List.length(&2, String, xs) : Nat}:
  %add_zero_right(List.length(&2, String, xs)) :
    {List.length(&2, String, List.reverse.go(&2, String, xs, Nil{}))
      == _ : Nat}
  length_reverse_go(xs, Nil{})

def operands_reverse_go(xs: List<&2, Cli.ScanEvent>,
    acc: List<&2, Cli.ScanEvent>) ->
    {List.reverse.go(&2, String, Laws.operands(xs), Laws.operands(acc))
      == Laws.operands(List.reverse.go(&2, Cli.ScanEvent, xs, acc))
      : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case Cli.FlagHit{id, value} <> xt:
      operands_reverse_go(xt, Cli.FlagHit{id, value} <> acc)
    case Cli.CountHit{id} <> xt:
      operands_reverse_go(xt, Cli.CountHit{id} <> acc)
    case Cli.ValueHit{id, value} <> xt:
      operands_reverse_go(xt, Cli.ValueHit{id, value} <> acc)
    case Cli.Operand{token} <> xt:
      operands_reverse_go(xt, Cli.Operand{token} <> acc)
    case Cli.Enter{name} <> xt:
      operands_reverse_go(xt, Cli.Enter{name} <> acc)
    case Cli.HelpHit{long} <> xt:
      operands_reverse_go(xt, Cli.HelpHit{long} <> acc)
    case Cli.VersionHit{} <> xt:
      operands_reverse_go(xt, Cli.VersionHit{} <> acc)

def reverse_go_twice(xs: List<&2, String>, acc: List<&2, String>) ->
    {List.reverse.go(&2, String, acc, xs)
      == List.reverse.go(&2, String,
        List.reverse.go(&2, String, xs, acc), Nil{}) : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case x <> xt: reverse_go_twice(xt, x <> acc)

def pushes(ts: List<&2, String>, acc: List<&2, Cli.ScanEvent>) ->
    List<&2, Cli.ScanEvent>:
  match ts:
    case Nil{}: acc
    case t <> rest: pushes(rest, Cli.Operand{t} <> acc)

def operands_pushes(ts: List<&2, String>, acc: List<&2, Cli.ScanEvent>) ->
    {List.reverse.go(&2, String, ts, Laws.operands(acc))
      == Laws.operands(pushes(ts, acc)) : List<&2, String>}:
  match ts:
    case Nil{}: {==}
    case t <> rest: operands_pushes(rest, Cli.Operand{t} <> acc)

def suffix_pushes(+post: List<&2, String>, +events: List<&2, Cli.ScanEvent>) ->
    {Laws.has_suffix(post, Laws.operands(
      List.reverse(&2, Cli.ScanEvent, pushes(post, events)))) == True{} : Bool}:
  %operands_reverse_go(pushes(post, events), Nil{}) :
    {Laws.same_strings(List.reverse(&2, String, post),
      List.take(&2, String, List.reverse(&2, String, _),
        List.length(&2, String, post))) == True{} : Bool}
  %operands_pushes(post, events) :
    {Laws.same_strings(List.reverse(&2, String, post),
      List.take(&2, String,
        List.reverse(&2, String, List.reverse.go(&2, String, _, Nil{})),
        List.length(&2, String, post))) == True{} : Bool}
  %reverse_go_twice(
    List.reverse.go(&2, String, post, Laws.operands(events)), Nil{}) :
    {Laws.same_strings(List.reverse(&2, String, post),
      List.take(&2, String, _, List.length(&2, String, post)))
      == True{} : Bool}
  %length_reverse(post) :
    {Laws.same_strings(List.reverse(&2, String, post),
      List.take(&2, String,
        List.reverse.go(&2, String, post, Laws.operands(events)), _))
      == True{} : Bool}
  same_take_reverse(post, Nil{}, Laws.operands(events))

def state_events(state: Cli.ScanState) -> List<&2, Cli.ScanEvent>:
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}:
      events

def state_issue(state: Cli.ScanState) -> Maybe<&2, Cli.ScanFault>:
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}:
      issue

def operand_go(ts: List<&2, String>, state: Cli.ScanState) ->
    Cli.ScanState:
  match ts:
    case Nil{}: state
    case t <> rest: operand_go(rest, Cli.scan_operand(state, t))

def first_issue_some(issue: Maybe<&2, Cli.ScanFault>, fault: Cli.ScanFault) ->
    {Maybe.is_some(&2, Cli.ScanFault, Cli.first_issue(issue, fault))
      == True{} : Bool}:
  match issue:
    case None{}: {==}
    case Some{old}: {==}

def operand_fault_case(take: Bool, scope: Cli.Scope,
    events: List<&2, Cli.ScanEvent>, resting: Bool, count: Nat,
    external: Maybe<&2, Cli.ExternalArgs>, +issue: Maybe<&2, Cli.ScanFault>,
    +t: String,
    held: {Maybe.is_some(&2, Cli.ScanFault, issue) == True{} : Bool}) ->
    {Maybe.is_some(&2, Cli.ScanFault, state_issue(Cli.scan_operand_case(
      take, Cli.ScanState{scope, events, resting, count, external, issue},
      t))) == True{} : Bool}:
  match take:
    case True{}: held
    case False{}: first_issue_some(issue, Cli.E09{t})

def operand_fault(state: Cli.ScanState, +t: String,
    held: {Maybe.is_some(&2, Cli.ScanFault, state_issue(state))
      == True{} : Bool}) ->
    {Maybe.is_some(&2, Cli.ScanFault,
      state_issue(Cli.scan_operand(state, t))) == True{} : Bool}:
  match state:
    case Cli.ScanState{+scope, events, resting, +count, external, issue}:
      operand_fault_case(Cli.scope_can_take(scope, count), scope, events,
        resting, count, external, issue, t, held)

def operands_fault(ts: List<&2, String>, +state: Cli.ScanState,
    held: {Maybe.is_some(&2, Cli.ScanFault, state_issue(state))
      == True{} : Bool}) ->
    {Maybe.is_some(&2, Cli.ScanFault, state_issue(operand_go(ts, state)))
      == True{} : Bool}:
  match ts:
    case Nil{}: held
    case +t <> rest:
      operands_fault(rest, Cli.scan_operand(state, t),
        operand_fault(state, t, held))

def none_some_absurd(m: Maybe<&2, Cli.ScanFault>,
    none: {Maybe.is_none(&2, Cli.ScanFault, m) == True{} : Bool},
    some: {Maybe.is_some(&2, Cli.ScanFault, m) == True{} : Bool}) -> Empty:
  match m:
    case None{}: false_true_absurd(some)
    case Some{fault}: false_true_absurd(none)

def operand_events_case(take: Bool, +scope: Cli.Scope,
    +events: List<&2, Cli.ScanEvent>, +resting: Bool, +count: Nat,
    +external: Maybe<&2, Cli.ExternalArgs>,
    +issue: Maybe<&2, Cli.ScanFault>, +t: String, +rest: List<&2, String>,
    clean: {Maybe.is_none(&2, Cli.ScanFault, state_issue(operand_go(rest,
      Cli.scan_operand_case(take,
        Cli.ScanState{scope, events, resting, count, external, issue}, t))))
      == True{} : Bool},
    step: {Maybe.is_none(&2, Cli.ScanFault, state_issue(operand_go(rest,
      Cli.scan_operand_case(take,
        Cli.ScanState{scope, events, resting, count, external, issue}, t))))
      == True{} : Bool} ->
      {pushes(rest, state_events(Cli.scan_operand_case(take,
        Cli.ScanState{scope, events, resting, count, external, issue}, t)))
        == state_events(operand_go(rest, Cli.scan_operand_case(take,
          Cli.ScanState{scope, events, resting, count, external, issue}, t)))
        : List<&2, Cli.ScanEvent>}) ->
    {pushes(rest, Cli.Operand{t} <> events)
      == state_events(operand_go(rest, Cli.scan_operand_case(take,
        Cli.ScanState{scope, events, resting, count, external, issue}, t)))
      : List<&2, Cli.ScanEvent>}:
  match take:
    case True{}: step(clean)
    case False{}:
      Empty.absurd({pushes(rest, Cli.Operand{t} <> events)
        == state_events(operand_go(rest, Cli.scan_error(
          Cli.ScanState{scope, events, resting, count, external, issue},
          Cli.E09{t}))) : List<&2, Cli.ScanEvent>},
        none_some_absurd(state_issue(operand_go(rest, Cli.scan_error(
          Cli.ScanState{scope, events, resting, count, external, issue},
          Cli.E09{t}))), clean,
          operands_fault(rest, Cli.scan_error(
            Cli.ScanState{scope, events, resting, count, external, issue},
            Cli.E09{t}), first_issue_some(issue, Cli.E09{t}))))

def operand_events(ts: List<&2, String>, state: Cli.ScanState,
    clean: {Maybe.is_none(&2, Cli.ScanFault, state_issue(operand_go(ts,
      state))) == True{} : Bool}) ->
    {pushes(ts, state_events(state)) == state_events(operand_go(ts, state))
      : List<&2, Cli.ScanEvent>}:
  match ts:
    case Nil{}: {==}
    case +t <> +rest:
      match state:
        case Cli.ScanState{+scope, +events, +resting, +count, +external,
            +issue}:
          operand_events_case(Cli.scope_can_take(scope, count), scope,
            events, resting, count, external, issue, t, rest, clean,
            next => operand_events(rest, Cli.scan_operand_case(
              Cli.scope_can_take(scope, count),
              Cli.ScanState{scope, events, resting, count, external, issue},
              t), next))

def scan_operands(ts: List<&2, String>, state: Cli.ScanState, ended: Bool) ->
    {Cli.Operands{operand_go(ts, state), ended}
      == Cli.scan_go(ts, Cli.Operands{state, ended}) : Cli.Mode}:
  match ts:
    case Nil{}: {==}
    case +t <> rest:
      scan_operands(rest, Cli.scan_operand(state, t), ended)

def p9_seen(+pre: List<&2, String>, post: List<&2, String>,
    trace: Cli.ScanTrace,
    dash: {True{} == List.contains(~String, ~String.eq, pre, "--")
      : Bool}) ->
    {Laws.p9_trace(pre, post, trace) == True{} : Bool}:
  match trace:
    case Cli.ScanTrace{path, events, ended, external, issue}:
      %dash :
        {Bool.or(Bool.not(Bool.and(Bool.not(_),
          Bool.and(ended, Maybe.is_none(&2, Cli.ScanFault, issue)))),
          Laws.has_suffix(post, Laws.operands(events))) == True{} : Bool}
      {==}

def p9_unended(pre: List<&2, String>, post: List<&2, String>,
    state: Cli.ScanState,
    clear: {False{} == List.contains(~String, ~String.eq, pre, "--")
      : Bool}) ->
    {Laws.p9_trace(pre, post, Cli.scan_trace_of(state, False{}))
      == True{} : Bool}:
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}:
      match scope:
        case Cli.Scope{path, spec}:
          %clear :
            {Bool.or(Bool.not(Bool.and(Bool.not(_),
              Bool.and(False{}, Maybe.is_none(&2, Cli.ScanFault, issue)))),
              Laws.has_suffix(post, Laws.operands(
                List.reverse(&2, Cli.ScanEvent, events)))) == True{} : Bool}
          {==}

def p9_close_case(ended: Bool, issue: Maybe<&2, Cli.ScanFault>,
    post: List<&2, String>, events: List<&2, Cli.ScanEvent>,
    found: {Maybe.is_none(&2, Cli.ScanFault, issue) == True{} : Bool} ->
      {Laws.has_suffix(post, Laws.operands(
        List.reverse(&2, Cli.ScanEvent, events))) == True{} : Bool}) ->
    {Bool.or(Bool.not(Bool.and(ended,
      Maybe.is_none(&2, Cli.ScanFault, issue))),
      Laws.has_suffix(post, Laws.operands(
        List.reverse(&2, Cli.ScanEvent, events)))) == True{} : Bool}:
  match ended issue:
    case True{} None{}: found({==})
    case True{} Some{fault}: {==}
    case False{} _: {==}

def p9_close(pre: List<&2, String>, post: List<&2, String>,
    state: Cli.ScanState, ended: Bool,
    clear: {False{} == List.contains(~String, ~String.eq, pre, "--")
      : Bool},
    found: {Maybe.is_none(&2, Cli.ScanFault, state_issue(state))
      == True{} : Bool} ->
      {Laws.has_suffix(post, Laws.operands(List.reverse(&2, Cli.ScanEvent,
        state_events(state)))) == True{} : Bool}) ->
    {Laws.p9_trace(pre, post, Cli.scan_trace_of(state, ended))
      == True{} : Bool}:
  match state:
    case Cli.ScanState{scope, +events, resting, count, external, +issue}:
      match scope:
        case Cli.Scope{path, spec}:
          %clear :
            {Bool.or(Bool.not(Bool.and(Bool.not(_),
              Bool.and(ended, Maybe.is_none(&2, Cli.ScanFault, issue)))),
              Laws.has_suffix(post, Laws.operands(
                List.reverse(&2, Cli.ScanEvent, events)))) == True{} : Bool}
          p9_close_case(ended, issue, post, events, found)

def p9_suffix(+post: List<&2, String>, +state: Cli.ScanState,
    found: {Maybe.is_none(&2, Cli.ScanFault,
      state_issue(operand_go(post, state))) == True{} : Bool}) ->
    {Laws.has_suffix(post, Laws.operands(List.reverse(&2, Cli.ScanEvent,
      state_events(operand_go(post, state))))) == True{} : Bool}:
  %operand_events(post, state, found) :
    {Laws.has_suffix(post, Laws.operands(
      List.reverse(&2, Cli.ScanEvent, _))) == True{} : Bool}
  suffix_pushes(post, state_events(state))

def p9_operands(pre: List<&2, String>, +post: List<&2, String>,
    +state: Cli.ScanState, +ended: Bool,
    clear: {False{} == List.contains(~String, ~String.eq, pre, "--")
      : Bool}) ->
    {Laws.p9_trace(pre, post,
      Cli.scan_trace(Cli.scan_go(post, Cli.Operands{state, ended})))
      == True{} : Bool}:
  %scan_operands(post, state, ended) :
    {Laws.p9_trace(pre, post, Cli.scan_trace(_)) == True{} : Bool}
  p9_close(pre, post, operand_go(post, state), ended, clear,
    found => p9_suffix(post, state, found))

def p9_closed(ts: List<&2, String>, pre: List<&2, String>,
    post: List<&2, String>, tail: Cli.Tail,
    clear: {False{} == List.contains(~String, ~String.eq, pre, "--")
      : Bool}) ->
    {Laws.p9_trace(pre, post,
      Cli.scan_trace(Cli.scan_go(ts, Cli.Closed{tail}))) == True{} : Bool}:
  match ts:
    case Nil{}: p9_unended(pre, post, Cli.scan_tail_close(tail), clear)
    case t <> rest: p9_closed(rest, pre, post, Cli.scan_tail(tail, t), clear)

def p9_dash(pre: List<&2, String>, +post: List<&2, String>, mode: Cli.Mode,
    clear: {False{} == List.contains(~String, ~String.eq, pre, "--")
      : Bool}) ->
    {Laws.p9_trace(pre, post,
      Cli.scan_trace(Cli.scan_go("--" <> post, mode))) == True{} : Bool}:
  match mode:
    case Cli.Open{state}: p9_operands(pre, post, state, True{}, clear)
    case Cli.Fetch{state, info}:
      p9_closed(post, pre, post, Cli.scan_faulted(Cli.scan_error(state,
        Cli.E03{Cli.arg_display(info)}), "--"), clear)
    case Cli.Operands{state, ended}:
      p9_operands(pre, post, Cli.scan_operand(state, "--"), ended, clear)
    case Cli.Capture{state, name}:
      p9_unended(pre, post, Cli.scan_external(state, name, "--" <> post),
        clear)
    case Cli.Closed{tail}:
      p9_closed(post, pre, post, Cli.scan_tail(tail, "--"), clear)

# List.contains on a cons is List.any.if over the head's test, with the
# rest's search delayed until the head misses.
def any_false_left(b: Bool, -c: Bool,
    e: {False{} == List.any.if(u => c, b) : Bool}) -> {False{} == b : Bool}:
  match b:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, false_true_absurd(e))
    case False{}: {==}

def any_false_right(b: Bool, -c: Bool,
    e: {False{} == List.any.if(u => c, b) : Bool}) -> {False{} == c : Bool}:
  match b:
    case True{}:
      Empty.absurd({False{} == c : Bool}, false_true_absurd(e))
    case False{}: e

def any_if_or(b: Bool, -c: Bool) ->
    {Bool.or(b, c) == List.any.if(u => c, b) : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def contains_cons(+x: String, t: List<&2, String>, +q: String) ->
    {Bool.or(String.eq(x, q), List.contains(~String, ~String.eq, t, q))
      == List.contains(~String, ~String.eq, x <> t, q) : Bool}:
  any_if_or(String.eq(x, q), List.contains(~String, ~String.eq, t, q))

def p9_before(pre: List<&2, String>, q: List<&2, String>,
    +post: List<&2, String>, mode: Cli.Mode,
    clear: {False{} == List.contains(~String, ~String.eq, q, "--") : Bool},
    +free: {False{} == List.contains(~String, ~String.eq, pre, "--")
      : Bool}) ->
    {Laws.p9_trace(q, post, Cli.scan_trace(Cli.scan_go(
      List.append(&2, String, pre, "--" <> post), mode))) == True{} : Bool}:
  match pre:
    case Nil{}: p9_dash(q, post, mode, clear)
    case +t <> +rest:
      match mode:
        case Cli.Open{state}:
          %any_false_left(String.eq(t, "--"),
            List.contains(~String, ~String.eq, rest, "--"), free) :
            {Laws.p9_trace(q, post, Cli.scan_trace(Cli.scan_go(
              List.append(&2, String, rest, "--" <> post),
              Cli.scan_open(_, state, t)))) == True{} : Bool}
          p9_before(rest, q, post, Cli.scan_token(t, state), clear,
            any_false_right(String.eq(t, "--"),
              List.contains(~String, ~String.eq, rest, "--"), free))
        case Cli.Fetch{state, info}:
          p9_before(rest, q, post, Cli.scan_fetch(state, info, t), clear,
            any_false_right(String.eq(t, "--"),
              List.contains(~String, ~String.eq, rest, "--"), free))
        case Cli.Operands{state, ended}:
          p9_before(rest, q, post,
            Cli.Operands{Cli.scan_operand(state, t), ended}, clear,
            any_false_right(String.eq(t, "--"),
              List.contains(~String, ~String.eq, rest, "--"), free))
        case Cli.Capture{state, name}:
          p9_unended(q, post, Cli.scan_external(state, name,
            t <> List.append(&2, String, rest, "--" <> post)), clear)
        case Cli.Closed{tail}:
          p9_before(rest, q, post, Cli.Closed{Cli.scan_tail(tail, t)},
            clear, any_false_right(String.eq(t, "--"),
              List.contains(~String, ~String.eq, rest, "--"), free))

def p9_split(dash: Bool, +pre: List<&2, String>, +post: List<&2, String>,
    mode: Cli.Mode,
    +seen: {dash == List.contains(~String, ~String.eq, pre, "--")
      : Bool}) ->
    {Laws.p9_trace(pre, post, Cli.scan_trace(Cli.scan_go(
      List.append(&2, String, pre, "--" <> post), mode))) == True{} : Bool}:
  match dash:
    case True{}:
      p9_seen(pre, post, Cli.scan_trace(Cli.scan_go(
        List.append(&2, String, pre, "--" <> post), mode)), seen)
    case False{}: p9_before(pre, pre, post, mode, seen, seen)

def Laws.p9(c, pre, post):
  p9_split(List.contains(~String, ~String.eq, pre, "--"), pre, post,
    Cli.Open{Cli.scan_start(c)}, {==})

def Laws.g_lex_cluster():
  {==}

def Laws.g_lex_values():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))

def Laws.g_lex_end():
  ({==}, {==})

def Laws.g_lex_count():
  ({==}, {==})

def Laws.g_lex_negation():
  ({==}, ({==}, {==}))

def Laws.g_lex_alias():
  {==}

def Laws.g_lex_bare():
  {==}

def Laws.g_lex_errors():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_lex_recovery():
  {==}

def Laws.g_pos_variadic():
  ({==}, ({==}, {==}))

def Laws.g_pos_cases():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))

def Laws.g_sub_descent():
  ({==}, ({==}, {==}))

def Laws.g_sub_alias():
  {==}

def Laws.g_sub_deep_globals():
  ({==}, {==})

def Laws.g_sub_own_ids():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.g_sub_help():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_sub_scope_errors():
  ({==}, ({==}, {==}))

def Laws.g_sub_external():
  ({==}, {==})

def Laws.g_sub_missing():
  ({==}, ({==}, {==}))

def Laws.g_sub_short_shadow():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_sub_digit_global():
  ({==}, ({==}, {==}))

def Laws.g_val_strings():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_val_nat():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_val_u32():
  ({==}, ({==}, {==}))

def Laws.g_val_f32():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.g_val_bool():
  ({==}, ({==}, {==}))

def Laws.g_val_one_of():
  ({==}, {==})

def Laws.g_val_delim():
  ({==}, {==})

def Laws.g_val_delim_typed():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))

def Laws.g_src_env():
  {==}

def Laws.g_src_empty_default():
  {==}

def Laws.g_src_precedence():
  ({==}, ({==}, {==}))

def Laws.g_src_invalid():
  ({==}, {==})

def Laws.g_src_env_names():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))

def Laws.g_rel_required():
  ({==}, {==})

def Laws.g_rel_need_one():
  ({==}, ({==}, {==}))

def Laws.g_rel_exclusive():
  {==}

def Laws.g_rel_conflict_order():
  ({==}, {==})

def Laws.g_rel_requires():
  ({==}, {==})

def Laws.g_rel_defaults():
  ({==}, {==})

def Laws.g_rel_global_groups():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))

def Laws.g_rel_global_groups_scope():
  ({==}, ({==}, ({==}, {==})))

def check_same(~T: Data, ~get: Cli.Field -> T, v: Maybe<&2, String>,
    f1: List<&2, Cli.Field>, f2: List<&2, Cli.Field>, id: String) ->
    {Laws.bug_of(T, Cli.read_check(~T, ~get, v, f1, id)) ==
      Laws.bug_of(T, Cli.read_check(~T, ~get, v, f2, id))
      : Maybe<&2, String>}:
  match v:
    case None{}: {==}
    case Some{msg}: {==}

def read_same(~T: Data, ~get: Cli.Field -> T, want: Cli.Want, c: Cli.Cmd,
    path: List<&2, String>, f1: List<&2, Cli.Field>,
    x1: Maybe<&2, Cli.ExternalArgs>, f2: List<&2, Cli.Field>,
    x2: Maybe<&2, Cli.ExternalArgs>, +id: String) ->
    {Laws.bug_of(T, Cli.read_with(~T, ~get, want,
      Cli.Matches{c, path, f1, x1}, id)) ==
      Laws.bug_of(T, Cli.read_with(~T, ~get, want,
        Cli.Matches{c, path, f2, x2}, id)) : Maybe<&2, String>}:
  check_same(~T, ~get, Cli.verdict(c, path, id, want), f1, f2, id)

def opt_choice_ok(-A: Data, found: Maybe<&2, A>) ->
    {None{} == Laws.bug_of(Maybe<&2, A>, Cli.choice_dec(A, found))
      : Maybe<&2, String>}:
  match found:
    case Some{value}: {==}
    case None{}: {==}

def opt_ok(-A: Data, keys: List<&2, String>, values: List<&2, A>,
    f: Cli.Field) ->
    {None{} == Laws.bug_of(Maybe<&2, A>,
      Cli.choose_read(A, keys, values, f)) : Maybe<&2, String>}:
  match f:
    case Cli.Field{id, head <> tail, source}:
      opt_choice_ok(A, Cli.find_by_key(&2, A, keys, values, head))
    case Cli.Field{id, Nil{}, source}: {==}

def must_bug(-A: Data, d: Cli.Dec(Maybe<&2, A>)) ->
    {Laws.bug_of(Maybe<&2, A>, d) == Laws.bug_of(A, Cli.choice_must(A, d))
      : Maybe<&2, String>}:
  match d:
    case Fail{Cli.Bug{msg}}: {==}
    case Fail{Cli.Usage{msg}}: {==}
    case Done{Some{value}}: {==}
    case Done{None{}}: {==}

def choose_opt_same(-A: Data, v: Maybe<&2, String>,
    +keys: List<&2, String>, +values: List<&2, A>,
    f1: List<&2, Cli.Field>, f2: List<&2, Cli.Field>, +id: String) ->
    {Laws.bug_of(Maybe<&2, A>, Cli.choose_check(A, v, keys, values, f1, id))
      == Laws.bug_of(Maybe<&2, A>,
        Cli.choose_check(A, v, keys, values, f2, id))
      : Maybe<&2, String>}:
  match v:
    case Some{msg}: {==}
    case None{}:
      %opt_ok(A, keys, values, Cli.field_find(f1, id)) :
        {_ == Laws.bug_of(Maybe<&2, A>,
          Cli.choose_read(A, keys, values, Cli.field_find(f2, id)))
          : Maybe<&2, String>}
      opt_ok(A, keys, values, Cli.field_find(f2, id))

def unzip_choose(keys: List<&2, String>) ->
    {(keys, keys) == Cli.unzip_keyed(&2, String, Laws.choose_table(keys))
      : (List<&2, String> & List<&2, String>)}:
  match keys:
    case Nil{}: {==}
    case key <> tail:
      %unzip_choose(tail) :
        {(key <> tail, key <> tail) ==
          Cli.keyed_cons(&2, String, key, key, _)
          : (List<&2, String> & List<&2, String>)}
      {==}

def keep_calls(keys: List<&2, String>) -> List<Cli.Call(Cli.Matches)>:
  match keys:
    case Nil{}: Nil{}
    case key <> tail: (+m => Cli.keep(m)) <> keep_calls(tail)

def unzip_keep(keys: List<&2, String>) ->
    {(keys, keep_calls(keys)) ==
      Cli.unzip_keyed(&1, Cli.Call(Cli.Matches), Laws.keep_table(keys))
      : (List<&2, String> & List<Cli.Call(Cli.Matches)>)}:
  match keys:
    case Nil{}: {==}
    case key <> tail:
      %unzip_keep(tail) :
        {(key <> tail, keep_calls(key <> tail)) ==
          Cli.keyed_cons(&1, Cli.Call(Cli.Matches), key, +m => Cli.keep(m), _)
          : (List<&2, String> & List<Cli.Call(Cli.Matches)>)}
      {==}

def call_same(bad: Maybe<&2, String>, +m1: Cli.Matches, +m2: Cli.Matches) ->
    {Laws.bug_of(Cli.Matches,
      Cli.route_call(Cli.Matches, bad, +n => Cli.keep(n), m1)) ==
      Laws.bug_of(Cli.Matches,
        Cli.route_call(Cli.Matches, bad, +n => Cli.keep(n), m2))
      : Maybe<&2, String>}:
  match bad:
    case None{}: {==}
    case Some{key}: {==}

def keep_hit(hit: Bool, keys: List<&2, String>, +all: List<&2, String>,
    +key: String, c: Cli.Cmd, +path: List<&2, String>, +m1: Cli.Matches,
    +m2: Cli.Matches,
    rest: {Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
      Cli.find_by_key_go(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
        key, None{}), all, c, path, m1)) ==
      Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
        Cli.find_by_key_go(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
          key, None{}), all, c, path, m2)) : Maybe<&2, String>}) ->
    {Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
      Cli.find_by_key_go(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
        key, Cli.by_key_hit(&1, Cli.Call(Cli.Matches), hit,
          +n => Cli.keep(n))), all, c, path, m1)) ==
      Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
        Cli.find_by_key_go(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
          key, Cli.by_key_hit(&1, Cli.Call(Cli.Matches), hit,
            +n => Cli.keep(n))), all, c, path, m2)) : Maybe<&2, String>}:
  match hit keys c:
    case True{} Nil{} Cli.Cmd{name, about, items}:
      call_same(Cli.non_command(all, items), m1, m2)
    case True{} head <> tail Cli.Cmd{name, about, items}:
      call_same(Cli.non_command(all, items), m1, m2)
    case False{} _ _: rest

def keep_go(keys: List<&2, String>, +all: List<&2, String>, +key: String,
    +c: Cli.Cmd, +path: List<&2, String>, +m1: Cli.Matches,
    +m2: Cli.Matches) ->
    {Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
      Cli.find_by_key_go(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
        key, None{}), all, c, path, m1)) ==
      Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
        Cli.find_by_key_go(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
          key, None{}), all, c, path, m2)) : Maybe<&2, String>}:
  match keys:
    case Nil{}:
      match c:
        case Cli.Cmd{name, about, items}: {==}
    case +head <> +tail:
      keep_hit(Cli.same_text(head, key), tail, all, key, c, path, m1, m2,
        keep_go(tail, all, key, c, path, m1, m2))

def keep_ok(keys: List<&2, String>, +all: List<&2, String>, +key: String,
    +c: Cli.Cmd, +path: List<&2, String>, +m1: Cli.Matches,
    +m2: Cli.Matches) ->
    {Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
      Cli.find_by_key(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
        key), all, c, path, m1)) ==
      Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
        Cli.find_by_key(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
          key), all, c, path, m2)) : Maybe<&2, String>}:
  keep_go(keys, all, key, c, path, m1, m2)

type Rd is Data:
  RFlag{}
  RCount{}
  RStr{}
  RStrOpt{}
  RStrs{}
  RNat{}
  RNatOpt{}
  RNats{}
  RU32{}
  RU32Opt{}
  RU32s{}
  RF32{}
  RF32Opt{}
  RF32s{}
  RBool{}
  RBoolOpt{}
  RBools{}
  RGiven{}
  RSource{}
  RChoose{}
  RChooseOpt{}
  RRoute{}

def entry(r: Rd, +m: Cli.Matches, +id: String, +keys: List<&2, String>) ->
    Maybe<&2, String>:
  match r:
    case RFlag{}: Laws.bug_of(Bool, Cli.flag(m, id))
    case RCount{}: Laws.bug_of(Nat, Cli.count(m, id))
    case RStr{}: Laws.bug_of(String, Cli.str(m, id))
    case RStrOpt{}: Laws.bug_of(Maybe<&2, String>, Cli.str_opt(m, id))
    case RStrs{}: Laws.bug_of(List<&2, String>, Cli.strs(m, id))
    case RNat{}: Laws.bug_of(Nat, Cli.nat(m, id))
    case RNatOpt{}: Laws.bug_of(Maybe<&2, Nat>, Cli.nat_opt(m, id))
    case RNats{}: Laws.bug_of(List<&2, Nat>, Cli.nats(m, id))
    case RU32{}: Laws.bug_of(U32, Cli.u32(m, id))
    case RU32Opt{}: Laws.bug_of(Maybe<&2, U32>, Cli.u32_opt(m, id))
    case RU32s{}: Laws.bug_of(List<&2, U32>, Cli.u32s(m, id))
    case RF32{}: Laws.bug_of(F32, Cli.f32(m, id))
    case RF32Opt{}: Laws.bug_of(Maybe<&2, F32>, Cli.f32_opt(m, id))
    case RF32s{}: Laws.bug_of(List<&2, F32>, Cli.f32s(m, id))
    case RBool{}: Laws.bug_of(Bool, Cli.bool(m, id))
    case RBoolOpt{}: Laws.bug_of(Maybe<&2, Bool>, Cli.bool_opt(m, id))
    case RBools{}: Laws.bug_of(List<&2, Bool>, Cli.bools(m, id))
    case RGiven{}: Laws.bug_of(Bool, Cli.given(m, id))
    case RSource{}: Laws.bug_of(Cli.Src, Cli.source(m, id))
    case RChoose{}:
      Laws.bug_of(String, Cli.choose(String, m, id, Laws.choose_table(keys)))
    case RChooseOpt{}:
      Laws.bug_of(Maybe<&2, String>,
        Cli.choose_opt(String, m, id, Laws.choose_table(keys)))
    case RRoute{}:
      Laws.bug_of(Cli.Matches,
        Cli.route(Cli.Matches, m, Laws.keep_table(keys)))

def entries(rs: List<&2, Rd>, +m: Cli.Matches, +id: String,
    +keys: List<&2, String>) -> List<&2, Maybe<&2, String>>:
  match rs:
    case Nil{}: Nil{}
    case r <> tail: entry(r, m, id, keys) <> entries(tail, m, id, keys)

def readers() -> List<&2, Rd>:
  [RFlag{}, RCount{}, RStr{}, RStrOpt{}, RStrs{}, RNat{}, RNatOpt{}, RNats{}, RU32{}, RU32Opt{}, RU32s{}, RF32{}, RF32Opt{}, RF32s{}, RBool{}, RBoolOpt{}, RBools{}, RGiven{}, RSource{}, RChoose{}, RChooseOpt{}, RRoute{}]

def entry_same(r: Rd, +c: Cli.Cmd, +path: List<&2, String>,
    +f1: List<&2, Cli.Field>, x1: Maybe<&2, Cli.ExternalArgs>,
    +f2: List<&2, Cli.Field>, x2: Maybe<&2, Cli.ExternalArgs>, +id: String,
    +keys: List<&2, String>) ->
    {entry(r, Cli.Matches{c, path, f1, x1}, id, keys) ==
      entry(r, Cli.Matches{c, path, f2, x2}, id, keys) : Maybe<&2, String>}:
  match r:
    case RFlag{}:
      read_same(~Bool, ~(f => Cli.get_one(~Bool, ~Cli.true_of, f)), Cli.WFlag{},
        c, path, f1, x1, f2, x2, id)
    case RCount{}:
      read_same(~Nat, ~(f => Cli.get_one(~Nat, ~Cli.nat_of, f)), Cli.WCount{},
        c, path, f1, x1, f2, x2, id)
    case RStr{}:
      read_same(~String, ~(f => Cli.get_one(~String, ~(s => s), f)), Cli.WValue{"str", Cli.ReadOne{}},
        c, path, f1, x1, f2, x2, id)
    case RStrOpt{}:
      read_same(~Maybe<&2, String>, ~(f => Cli.get_opt(~String, ~(s => s), f)), Cli.WValue{"str", Cli.ReadOpt{}},
        c, path, f1, x1, f2, x2, id)
    case RStrs{}:
      read_same(~List<&2, String>, ~(f => Cli.get_many(~String, ~(s => s), f)), Cli.WValue{"str", Cli.ReadMany{}},
        c, path, f1, x1, f2, x2, id)
    case RNat{}:
      read_same(~Nat, ~(f => Cli.get_one(~Nat, ~Cli.nat_of, f)), Cli.WValue{"nat", Cli.ReadOne{}},
        c, path, f1, x1, f2, x2, id)
    case RNatOpt{}:
      read_same(~Maybe<&2, Nat>, ~(f => Cli.get_opt(~Nat, ~Cli.nat_of, f)), Cli.WValue{"nat", Cli.ReadOpt{}},
        c, path, f1, x1, f2, x2, id)
    case RNats{}:
      read_same(~List<&2, Nat>, ~(f => Cli.get_many(~Nat, ~Cli.nat_of, f)), Cli.WValue{"nat", Cli.ReadMany{}},
        c, path, f1, x1, f2, x2, id)
    case RU32{}:
      read_same(~U32, ~(f => Cli.get_one(~U32, ~Cli.u32_of, f)), Cli.WValue{"u32", Cli.ReadOne{}},
        c, path, f1, x1, f2, x2, id)
    case RU32Opt{}:
      read_same(~Maybe<&2, U32>, ~(f => Cli.get_opt(~U32, ~Cli.u32_of, f)), Cli.WValue{"u32", Cli.ReadOpt{}},
        c, path, f1, x1, f2, x2, id)
    case RU32s{}:
      read_same(~List<&2, U32>, ~(f => Cli.get_many(~U32, ~Cli.u32_of, f)), Cli.WValue{"u32", Cli.ReadMany{}},
        c, path, f1, x1, f2, x2, id)
    case RF32{}:
      read_same(~F32, ~(f => Cli.get_one(~F32, ~Cli.f32_of, f)), Cli.WValue{"f32", Cli.ReadOne{}},
        c, path, f1, x1, f2, x2, id)
    case RF32Opt{}:
      read_same(~Maybe<&2, F32>, ~(f => Cli.get_opt(~F32, ~Cli.f32_of, f)), Cli.WValue{"f32", Cli.ReadOpt{}},
        c, path, f1, x1, f2, x2, id)
    case RF32s{}:
      read_same(~List<&2, F32>, ~(f => Cli.get_many(~F32, ~Cli.f32_of, f)), Cli.WValue{"f32", Cli.ReadMany{}},
        c, path, f1, x1, f2, x2, id)
    case RBool{}:
      read_same(~Bool, ~(f => Cli.get_one(~Bool, ~Cli.env_bool_true, f)), Cli.WValue{"bool", Cli.ReadOne{}},
        c, path, f1, x1, f2, x2, id)
    case RBoolOpt{}:
      read_same(~Maybe<&2, Bool>, ~(f => Cli.get_opt(~Bool, ~Cli.env_bool_true, f)), Cli.WValue{"bool", Cli.ReadOpt{}},
        c, path, f1, x1, f2, x2, id)
    case RBools{}:
      read_same(~List<&2, Bool>, ~(f => Cli.get_many(~Bool, ~Cli.env_bool_true, f)), Cli.WValue{"bool", Cli.ReadMany{}},
        c, path, f1, x1, f2, x2, id)
    case RGiven{}:
      read_same(~Bool, ~(f => Cli.source_given(Cli.field_src(f))), Cli.WAny{},
        c, path, f1, x1, f2, x2, id)
    case RSource{}:
      read_same(~Cli.Src, ~(Cli.field_src), Cli.WAny{},
        c, path, f1, x1, f2, x2, id)
    case RChoose{}:
      %unzip_choose(keys) :
        {Laws.bug_of(String, Cli.choice_must(String, Cli.choose_pick(String,
          False{}, _, Cli.Matches{c, path, f1, x1}, id))) ==
          Laws.bug_of(String, Cli.choice_must(String, Cli.choose_pick(String,
            False{}, _, Cli.Matches{c, path, f2, x2}, id)))
          : Maybe<&2, String>}
      %must_bug(String, Cli.choose_check(String,
          Cli.verdict(c, path, id, Cli.WChoose{False{}, keys}),
          keys, keys, f1, id)) :
        {_ == Laws.bug_of(String, Cli.choice_must(String,
          Cli.choose_check(String,
            Cli.verdict(c, path, id, Cli.WChoose{False{}, keys}),
            keys, keys, f2, id))) : Maybe<&2, String>}
      %must_bug(String, Cli.choose_check(String,
          Cli.verdict(c, path, id, Cli.WChoose{False{}, keys}),
          keys, keys, f2, id)) :
        {Laws.bug_of(Maybe<&2, String>, Cli.choose_check(String,
          Cli.verdict(c, path, id, Cli.WChoose{False{}, keys}),
          keys, keys, f1, id)) == _ : Maybe<&2, String>}
      choose_opt_same(String,
        Cli.verdict(c, path, id, Cli.WChoose{False{}, keys}),
        keys, keys, f1, f2, id)
    case RChooseOpt{}:
      %unzip_choose(keys) :
        {Laws.bug_of(Maybe<&2, String>, Cli.choose_pick(String, True{}, _,
          Cli.Matches{c, path, f1, x1}, id)) ==
          Laws.bug_of(Maybe<&2, String>, Cli.choose_pick(String, True{}, _,
            Cli.Matches{c, path, f2, x2}, id)) : Maybe<&2, String>}
      choose_opt_same(String,
        Cli.verdict(c, path, id, Cli.WChoose{True{}, keys}),
        keys, keys, f1, f2, id)
    case RRoute{}:
      %unzip_keep(keys) :
        {Laws.bug_of(Cli.Matches, Cli.route_pick(Cli.Matches, _,
          Cli.Matches{c, path, f1, x1})) ==
          Laws.bug_of(Cli.Matches, Cli.route_pick(Cli.Matches, _,
            Cli.Matches{c, path, f2, x2})) : Maybe<&2, String>}
      keep_ok(keys, keys, String.join(path, " "), c, path,
        Cli.Matches{c, path, f1, x1}, Cli.Matches{c, path, f2, x2})

def entries_same(rs: List<&2, Rd>, +c: Cli.Cmd, +path: List<&2, String>,
    +f1: List<&2, Cli.Field>, +x1: Maybe<&2, Cli.ExternalArgs>,
    +f2: List<&2, Cli.Field>, +x2: Maybe<&2, Cli.ExternalArgs>, +id: String,
    +keys: List<&2, String>) ->
    {entries(rs, Cli.Matches{c, path, f1, x1}, id, keys) ==
      entries(rs, Cli.Matches{c, path, f2, x2}, id, keys)
      : List<&2, Maybe<&2, String>>}:
  match rs:
    case Nil{}: {==}
    case r <> tail:
      %entry_same(r, c, path, f1, x1, f2, x2, id, keys) :
        {entry(r, Cli.Matches{c, path, f1, x1}, id, keys) <>
          entries(tail, Cli.Matches{c, path, f1, x1}, id, keys) ==
          _ <> entries(tail, Cli.Matches{c, path, f2, x2}, id, keys)
          : List<&2, Maybe<&2, String>>}
      %entries_same(tail, c, path, f1, x1, f2, x2, id, keys) :
        {entry(r, Cli.Matches{c, path, f1, x1}, id, keys) <>
          entries(tail, Cli.Matches{c, path, f1, x1}, id, keys) ==
          entry(r, Cli.Matches{c, path, f1, x1}, id, keys) <> _
          : List<&2, Maybe<&2, String>>}
      {==}

def p12_found(+c: Cli.Cmd, r: Cli.ParseResult, +id: String,
    +keys: List<&2, String>) -> Laws.p12_at(c, Cli.matches(c, r), id, keys):
  match r:
    case Cli.Accepted{+path, fields, external}:
      entries_same(readers(), c, path, fields, external,
        Cli.sample_fields(c, path), None{}, id, keys)
    case Cli.Rejected{path, fault}: Unit{}
    case Cli.HelpRequested{path, long}: Unit{}
    case Cli.VersionRequested{}: Unit{}
    case Cli.SummaryRequired{}: Unit{}

def Laws.p12(c, h, argv, id, keys):
  p12_found(c, Cli.parse(c, h, argv), id, keys)

def Laws.g_check_wrong_id():
  ({==}, ({==}, {==}))

def Laws.g_check_wrong_reader():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))

def Laws.g_check_absent():
  ({==}, ({==}, {==}))

def Laws.g_check_choose():
  ({==}, ({==}, {==}))

def Laws.g_check_route():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_check_samples():
  ({==}, {==})

def Laws.g_check_builtins():
  ({==}, {==})

def Laws.g_check_route_words():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))

# P18, P19 and P20: the first-match lookups agree with LAWS.bend's
# references. A match over an Item list names all 27 constructors: a
# wildcard arm leaves its head refined away from the named ones, which does
# not reduce.

# P18 text: String.eq is String.order's result at EQ, which a mismatched
# char fixes, as it fixes same_go's flag at False.
def same_go_false(a: String, b: String) ->
    {Cli.same_go(a, b, False{}) == False{} : Bool}:
  match a b:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{h, t}: {==}
    case SCon{h, t} SNil{}: {==}
    case SCon{x, xt} SCon{y, yt}: {==}

def order_lt(a: String, b: String) ->
    {LT{} == String.order.go(a, b, LT{}) : Cmp}:
  match a b:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{h, t}: {==}
    case SCon{h, t} SNil{}: {==}
    case SCon{Chr{x}, xt} SCon{Chr{y}, yt}: {==}

def order_gt(a: String, b: String) ->
    {GT{} == String.order.go(a, b, GT{}) : Cmp}:
  match a b:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{h, t}: {==}
    case SCon{h, t} SNil{}: {==}
    case SCon{Chr{x}, xt} SCon{Chr{y}, yt}: {==}

def text_step(+xt: String, +yt: String, c: Cmp) ->
    {Cli.same_go(xt, yt, True{}) == String.eq(xt, yt) : Bool} ->
    {Cli.same_go(xt, yt, Cmp.is_eq(c))
      == Cmp.is_eq(String.order.go(xt, yt, c)) : Bool}:
  match c:
    case LT{}:
      ih =>
        %order_lt(xt, yt) :
          {Cli.same_go(xt, yt, False{}) == Cmp.is_eq(_) : Bool}
        same_go_false(xt, yt)
    case EQ{}: ih => ih
    case GT{}:
      ih =>
        %order_gt(xt, yt) :
          {Cli.same_go(xt, yt, False{}) == Cmp.is_eq(_) : Bool}
        same_go_false(xt, yt)

def Laws.p18_text(a, b):
  match a b:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{h, t}: {==}
    case SCon{h, t} SNil{}: {==}
    case SCon{Chr{+p}, +xt} SCon{Chr{+q}, +yt}:
      text_step(xt, yt, U32.cmp(p, q), Laws.p18_text(xt, yt))

# P18 key: each walk below runs from the lookup's found so far, which stays
# once it is Some, and is the found so far or else the reference over the
# rest.
def key_pick(a, -A: Kind(a), hit: Bool, -v: A, -rest: Maybe<a, A>) ->
    {Bool.pick(Maybe<a, A>, hit, Some{v}, rest)
      == Maybe.or(a, A, Cli.by_key_hit(a, A, hit, v), rest) : Maybe<a, A>}:
  match hit:
    case True{}: {==}
    case False{}: {==}

def keyed_go(a, -A: Kind(a), keys: List<&2, String>, values: List<a, A>,
    +key: String, found: Maybe<a, A>) ->
    {Maybe.or(a, A, found, Laws.keyed(a, A, keys, values, key))
      == Cli.find_by_key_go(a, A, keys, values, key, found) : Maybe<a, A>}:
  match keys values found:
    case Nil{} Nil{} None{}: {==}
    case Nil{} Nil{} Some{h}: {==}
    case Nil{} v <> vt None{}: {==}
    case Nil{} v <> vt Some{h}: {==}
    case k <> kt Nil{} None{}: {==}
    case k <> kt Nil{} Some{h}: {==}
    case k <> kt v <> vt Some{h}: {==}
    case +k <> kt v <> vt None{}:
      %keyed_go(a, A, kt, vt, key,
        Cli.by_key_hit(a, A, Cli.same_text(k, key), v)) :
        {Bool.pick(Maybe<a, A>, String.eq(k, key), Some{v},
          Laws.keyed(a, A, kt, vt, key)) == _ : Maybe<a, A>}
      %Laws.p18_text(k, key) :
        {Bool.pick(Maybe<a, A>, _, Some{v}, Laws.keyed(a, A, kt, vt, key))
          == Maybe.or(a, A, Cli.by_key_hit(a, A, Cli.same_text(k, key), v),
            Laws.keyed(a, A, kt, vt, key)) : Maybe<a, A>}
      key_pick(a, A, Cli.same_text(k, key), v, Laws.keyed(a, A, kt, vt, key))

def Laws.p18_key(a, A, keys, values, key):
  %keyed_go(a, A, keys, values, key, None{}) :
    {_ == Laws.keyed(a, A, keys, values, key) : Maybe<a, A>}
  {==}

# P18 field.
def field_pick(hit: Bool, -f: Cli.Field, -rest: Cli.Field) ->
    {Bool.pick(Cli.Field, hit, f, rest) == Maybe.default(&2, Cli.Field,
      Bool.pick(Maybe<&2, Cli.Field>, hit, Some{f}, None{}), rest)
      : Cli.Field}:
  match hit:
    case True{}: {==}
    case False{}: {==}

def field_go(fields: List<&2, Cli.Field>, +id: String,
    found: Maybe<&2, Cli.Field>) ->
    {Maybe.default(&2, Cli.Field, found, Laws.field_ref(fields, id))
      == Cli.field_seek(fields, id, found) : Cli.Field}:
  match fields found:
    case Nil{} None{}: {==}
    case Nil{} Some{f}: {==}
    case f <> tail Some{g}: {==}
    case Cli.Field{+key, values, source} <> tail None{}:
      %field_go(tail, id, Bool.pick(Maybe<&2, Cli.Field>,
        Cli.same_text(key, id), Some{Cli.Field{key, values, source}},
        None{})) :
        {Bool.pick(Cli.Field, String.eq(key, id),
          Cli.Field{key, values, source}, Laws.field_ref(tail, id)) == _
          : Cli.Field}
      %Laws.p18_text(key, id) :
        {Bool.pick(Cli.Field, _, Cli.Field{key, values, source},
          Laws.field_ref(tail, id)) == Maybe.default(&2, Cli.Field,
            Bool.pick(Maybe<&2, Cli.Field>, Cli.same_text(key, id),
              Some{Cli.Field{key, values, source}}, None{}),
            Laws.field_ref(tail, id)) : Cli.Field}
      field_pick(Cli.same_text(key, id), Cli.Field{key, values, source},
        Laws.field_ref(tail, id))

def Laws.p18_field(fields, id):
  %field_go(fields, id, None{}) :
    {_ == Laws.field_ref(fields, id) : Cli.Field}
  {==}

# P18 sub: has_alias from found is found or aliases_name.
# Arms: python3 tools/ctorarms.py --prefix Cli. cli.bend Item '$P <> tail True{}' '{==}'
# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Alias cli.bend Item '$P <> tail False{}' 'alias_go(tail, q, False{})'
def alias_go(items: List<&2, Cli.Item>, +q: String, found: Bool) ->
    {Bool.or(found, Laws.aliases_name(items, q))
      == Cli.has_alias(items, q, found) : Bool}:
  match items found:
    case Nil{} True{}: {==}
    case Nil{} False{}: {==}
    case Cli.Arg{x0, x1, x2} <> tail True{}: {==}
    case Cli.Sub{x0, x1, x2} <> tail True{}: {==}
    case Cli.Version{x0} <> tail True{}: {==}
    case Cli.Alias{x0} <> tail True{}: {==}
    case Cli.Hidden{} <> tail True{}: {==}
    case Cli.Example{x0, x1} <> tail True{}: {==}
    case Cli.After{x0} <> tail True{}: {==}
    case Cli.SubOptional{} <> tail True{}: {==}
    case Cli.External{} <> tail True{}: {==}
    case Cli.Exclusive{x0} <> tail True{}: {==}
    case Cli.NeedOne{x0} <> tail True{}: {==}
    case Cli.Id{x0} <> tail True{}: {==}
    case Cli.Required{} <> tail True{}: {==}
    case Cli.AttrDefault{x0} <> tail True{}: {==}
    case Cli.AttrEnv{x0} <> tail True{}: {==}
    case Cli.Global{} <> tail True{}: {==}
    case Cli.Heading{x0} <> tail True{}: {==}
    case Cli.As{x0} <> tail True{}: {==}
    case Cli.OneOf{x0} <> tail True{}: {==}
    case Cli.Delim{x0} <> tail True{}: {==}
    case Cli.Hyphen{} <> tail True{}: {==}
    case Cli.Rest{} <> tail True{}: {==}
    case Cli.Bare{x0} <> tail True{}: {==}
    case Cli.Conflicts{x0} <> tail True{}: {==}
    case Cli.Requires{x0} <> tail True{}: {==}
    case Cli.Group{x0} <> tail True{}: {==}
    case Cli.Builtin{} <> tail True{}: {==}
    case Cli.Alias{+name} <> tail False{}:
      %alias_go(tail, q, Cli.same_text(name, q)) :
        {Bool.or(String.eq(name, q), Laws.aliases_name(tail, q)) == _
          : Bool}
      %Laws.p18_text(name, q) :
        {Bool.or(_, Laws.aliases_name(tail, q))
          == Bool.or(Cli.same_text(name, q), Laws.aliases_name(tail, q))
          : Bool}
      {==}
    case Cli.Arg{x0, x1, x2} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Sub{x0, x1, x2} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Version{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Hidden{} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Example{x0, x1} <> tail False{}: alias_go(tail, q, False{})
    case Cli.After{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.SubOptional{} <> tail False{}: alias_go(tail, q, False{})
    case Cli.External{} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Exclusive{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.NeedOne{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Id{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Required{} <> tail False{}: alias_go(tail, q, False{})
    case Cli.AttrDefault{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.AttrEnv{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Global{} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Heading{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.As{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.OneOf{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Delim{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Hyphen{} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Rest{} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Bare{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Conflicts{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Requires{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Group{x0} <> tail False{}: alias_go(tail, q, False{})
    case Cli.Builtin{} <> tail False{}: alias_go(tail, q, False{})

def alias_pick(b: Bool, -name: String, -children: List<&2, Cli.Item>,
    -rest: Maybe<&2, Cli.SubFound>) ->
    {Bool.pick(Maybe<&2, Cli.SubFound>, b,
      Some{Cli.SubFound{name, children}}, rest)
      == Maybe.or(&2, Cli.SubFound, Cli.alias_hit(b, name, children), rest)
      : Maybe<&2, Cli.SubFound>}:
  match b:
    case True{}: {==}
    case False{}: {==}

def sub_pick(same: Bool, -name: String, +children: List<&2, Cli.Item>,
    +q: String, -rest: Maybe<&2, Cli.SubFound>) ->
    {Bool.pick(Maybe<&2, Cli.SubFound>,
      Bool.or(same, Laws.aliases_name(children, q)),
      Some{Cli.SubFound{name, children}}, rest)
      == Maybe.or(&2, Cli.SubFound, Cli.sub_hit(same, name, children, q),
        rest) : Maybe<&2, Cli.SubFound>}:
  match same:
    case True{}: {==}
    case False{}:
      %alias_go(children, q, False{}) :
        {Bool.pick(Maybe<&2, Cli.SubFound>,
          Bool.or(False{}, Laws.aliases_name(children, q)),
          Some{Cli.SubFound{name, children}}, rest)
          == Maybe.or(&2, Cli.SubFound, Cli.alias_hit(_, name, children),
            rest) : Maybe<&2, Cli.SubFound>}
      alias_pick(Laws.aliases_name(children, q), name, children, rest)

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Sub cli.bend Item '$P <> tail None{}' 'sub_go(tail, q, None{})'
def sub_go(items: List<&2, Cli.Item>, +q: String,
    found: Maybe<&2, Cli.SubFound>) ->
    {Maybe.or(&2, Cli.SubFound, found, Laws.sub_ref(items, q))
      == Cli.find_sub_go(items, q, found) : Maybe<&2, Cli.SubFound>}:
  match items found:
    case Nil{} None{}: {==}
    case Nil{} Some{h}: {==}
    case h <> tail Some{g}: {==}
    case Cli.Sub{+name, about, +children} <> tail None{}:
      %sub_go(tail, q, Cli.sub_hit(Cli.same_text(q, name), name, children,
        q)) :
        {Bool.pick(Maybe<&2, Cli.SubFound>,
          Bool.or(String.eq(q, name), Laws.aliases_name(children, q)),
          Some{Cli.SubFound{name, children}}, Laws.sub_ref(tail, q)) == _
          : Maybe<&2, Cli.SubFound>}
      %Laws.p18_text(q, name) :
        {Bool.pick(Maybe<&2, Cli.SubFound>,
          Bool.or(_, Laws.aliases_name(children, q)),
          Some{Cli.SubFound{name, children}}, Laws.sub_ref(tail, q))
          == Maybe.or(&2, Cli.SubFound, Cli.sub_hit(Cli.same_text(q, name),
            name, children, q), Laws.sub_ref(tail, q))
          : Maybe<&2, Cli.SubFound>}
      sub_pick(Cli.same_text(q, name), name, children, q,
        Laws.sub_ref(tail, q))
    case Cli.Arg{x0, x1, x2} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Version{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Alias{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Hidden{} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Example{x0, x1} <> tail None{}: sub_go(tail, q, None{})
    case Cli.After{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.SubOptional{} <> tail None{}: sub_go(tail, q, None{})
    case Cli.External{} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Exclusive{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.NeedOne{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Id{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Required{} <> tail None{}: sub_go(tail, q, None{})
    case Cli.AttrDefault{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.AttrEnv{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Global{} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Heading{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.As{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.OneOf{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Delim{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Hyphen{} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Rest{} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Bare{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Conflicts{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Requires{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Group{x0} <> tail None{}: sub_go(tail, q, None{})
    case Cli.Builtin{} <> tail None{}: sub_go(tail, q, None{})

def Laws.p18_sub(items, query):
  %sub_go(items, query, None{}) :
    {_ == Laws.sub_ref(items, query) : Maybe<&2, Cli.SubFound>}
  {==}

# P18 arg.
def arg_pick(hit: Bool, -info: Cli.ArgInfo,
    -rest: Maybe<&2, Cli.ArgInfo>) ->
    {Bool.pick(Maybe<&2, Cli.ArgInfo>, hit, Some{info}, rest)
      == Maybe.or(&2, Cli.ArgInfo,
        Bool.pick(Maybe<&2, Cli.ArgInfo>, hit, Some{info}, None{}), rest)
      : Maybe<&2, Cli.ArgInfo>}:
  match hit:
    case True{}: {==}
    case False{}: {==}

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Arg cli.bend Item '$P <> tail None{}' 'arg_go(tail, id, None{})'
def arg_go(items: List<&2, Cli.Item>, +id: String,
    found: Maybe<&2, Cli.ArgInfo>) ->
    {Maybe.or(&2, Cli.ArgInfo, found, Laws.arg_ref(items, id))
      == Cli.find_arg_go(items, id, found) : Maybe<&2, Cli.ArgInfo>}:
  match items found:
    case Nil{} None{}: {==}
    case Nil{} Some{h}: {==}
    case h <> tail Some{g}: {==}
    case Cli.Arg{+usage, help, +attrs} <> tail None{}:
      %arg_go(tail, id, Bool.pick(Maybe<&2, Cli.ArgInfo>,
        Cli.same_text(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Some{Cli.arg_info(usage, attrs)}, None{})) :
        {Bool.pick(Maybe<&2, Cli.ArgInfo>,
          String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
          Some{Cli.arg_info(usage, attrs)}, Laws.arg_ref(tail, id)) == _
          : Maybe<&2, Cli.ArgInfo>}
      %Laws.p18_text(Cli.info_id(Cli.arg_info(usage, attrs)), id) :
        {Bool.pick(Maybe<&2, Cli.ArgInfo>, _,
          Some{Cli.arg_info(usage, attrs)}, Laws.arg_ref(tail, id))
          == Maybe.or(&2, Cli.ArgInfo, Bool.pick(Maybe<&2, Cli.ArgInfo>,
            Cli.same_text(Cli.info_id(Cli.arg_info(usage, attrs)), id),
            Some{Cli.arg_info(usage, attrs)}, None{}),
            Laws.arg_ref(tail, id)) : Maybe<&2, Cli.ArgInfo>}
      arg_pick(Cli.same_text(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), Laws.arg_ref(tail, id))
    case Cli.Sub{x0, x1, x2} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Version{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Alias{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Hidden{} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Example{x0, x1} <> tail None{}: arg_go(tail, id, None{})
    case Cli.After{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.SubOptional{} <> tail None{}: arg_go(tail, id, None{})
    case Cli.External{} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Exclusive{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.NeedOne{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Id{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Required{} <> tail None{}: arg_go(tail, id, None{})
    case Cli.AttrDefault{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.AttrEnv{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Global{} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Heading{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.As{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.OneOf{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Delim{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Hyphen{} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Rest{} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Bare{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Conflicts{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Requires{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Group{x0} <> tail None{}: arg_go(tail, id, None{})
    case Cli.Builtin{} <> tail None{}: arg_go(tail, id, None{})

def Laws.p18_arg(items, id):
  %arg_go(items, id, None{}) :
    {_ == Laws.arg_ref(items, id) : Maybe<&2, Cli.ArgInfo>}
  {==}

# P19 arg: spec_items keeps each Arg's info and drops each Sub, and
# find_spec_info walks it as find_arg_go walks the items.
# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Sub cli.bend Item '$P <> tail' '{==}'
def spec_some(items: List<&2, Cli.Item>, +id: String, -h: Cli.ArgInfo) ->
    {Cli.find_spec_info(Cli.spec_items(items), id, Some{h}) == Some{h}
      : Maybe<&2, Cli.ArgInfo>}:
  match items:
    case Nil{}: {==}
    case Cli.Sub{x0, x1, x2} <> tail: spec_some(tail, id, h)
    case Cli.Arg{x0, x1, x2} <> tail: {==}
    case Cli.Version{x0} <> tail: {==}
    case Cli.Alias{x0} <> tail: {==}
    case Cli.Hidden{} <> tail: {==}
    case Cli.Example{x0, x1} <> tail: {==}
    case Cli.After{x0} <> tail: {==}
    case Cli.SubOptional{} <> tail: {==}
    case Cli.External{} <> tail: {==}
    case Cli.Exclusive{x0} <> tail: {==}
    case Cli.NeedOne{x0} <> tail: {==}
    case Cli.Id{x0} <> tail: {==}
    case Cli.Required{} <> tail: {==}
    case Cli.AttrDefault{x0} <> tail: {==}
    case Cli.AttrEnv{x0} <> tail: {==}
    case Cli.Global{} <> tail: {==}
    case Cli.Heading{x0} <> tail: {==}
    case Cli.As{x0} <> tail: {==}
    case Cli.OneOf{x0} <> tail: {==}
    case Cli.Delim{x0} <> tail: {==}
    case Cli.Hyphen{} <> tail: {==}
    case Cli.Rest{} <> tail: {==}
    case Cli.Bare{x0} <> tail: {==}
    case Cli.Conflicts{x0} <> tail: {==}
    case Cli.Requires{x0} <> tail: {==}
    case Cli.Group{x0} <> tail: {==}
    case Cli.Builtin{} <> tail: {==}

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Sub cli.bend Item '$P <> tail Some{h}' '{==}'
# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Arg cli.bend Item '$P <> tail None{}' 'spec_go(tail, id, None{})'
def spec_go(items: List<&2, Cli.Item>, +id: String,
    found: Maybe<&2, Cli.ArgInfo>) ->
    {Cli.find_spec_info(Cli.spec_items(items), id, found)
      == Cli.find_arg_go(items, id, found) : Maybe<&2, Cli.ArgInfo>}:
  match items found:
    case Nil{} None{}: {==}
    case Nil{} Some{h}: {==}
    case Cli.Sub{x0, x1, x2} <> tail Some{h}: spec_some(tail, id, h)
    case Cli.Arg{x0, x1, x2} <> tail Some{h}: {==}
    case Cli.Version{x0} <> tail Some{h}: {==}
    case Cli.Alias{x0} <> tail Some{h}: {==}
    case Cli.Hidden{} <> tail Some{h}: {==}
    case Cli.Example{x0, x1} <> tail Some{h}: {==}
    case Cli.After{x0} <> tail Some{h}: {==}
    case Cli.SubOptional{} <> tail Some{h}: {==}
    case Cli.External{} <> tail Some{h}: {==}
    case Cli.Exclusive{x0} <> tail Some{h}: {==}
    case Cli.NeedOne{x0} <> tail Some{h}: {==}
    case Cli.Id{x0} <> tail Some{h}: {==}
    case Cli.Required{} <> tail Some{h}: {==}
    case Cli.AttrDefault{x0} <> tail Some{h}: {==}
    case Cli.AttrEnv{x0} <> tail Some{h}: {==}
    case Cli.Global{} <> tail Some{h}: {==}
    case Cli.Heading{x0} <> tail Some{h}: {==}
    case Cli.As{x0} <> tail Some{h}: {==}
    case Cli.OneOf{x0} <> tail Some{h}: {==}
    case Cli.Delim{x0} <> tail Some{h}: {==}
    case Cli.Hyphen{} <> tail Some{h}: {==}
    case Cli.Rest{} <> tail Some{h}: {==}
    case Cli.Bare{x0} <> tail Some{h}: {==}
    case Cli.Conflicts{x0} <> tail Some{h}: {==}
    case Cli.Requires{x0} <> tail Some{h}: {==}
    case Cli.Group{x0} <> tail Some{h}: {==}
    case Cli.Builtin{} <> tail Some{h}: {==}
    case Cli.Arg{+usage, help, +attrs} <> tail None{}:
      spec_go(tail, id, Bool.pick(Maybe<&2, Cli.ArgInfo>,
        Cli.same_text(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Some{Cli.arg_info(usage, attrs)}, None{}))
    case Cli.Sub{x0, x1, x2} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Version{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Alias{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Hidden{} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Example{x0, x1} <> tail None{}: spec_go(tail, id, None{})
    case Cli.After{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.SubOptional{} <> tail None{}: spec_go(tail, id, None{})
    case Cli.External{} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Exclusive{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.NeedOne{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Id{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Required{} <> tail None{}: spec_go(tail, id, None{})
    case Cli.AttrDefault{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.AttrEnv{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Global{} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Heading{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.As{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.OneOf{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Delim{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Hyphen{} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Rest{} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Bare{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Conflicts{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Requires{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Group{x0} <> tail None{}: spec_go(tail, id, None{})
    case Cli.Builtin{} <> tail None{}: spec_go(tail, id, None{})

def Laws.p19_arg(items, id):
  spec_go(items, id, None{})

def Laws.p19_arg_order(items, globals, path):
  {==}

# P19 inherit: spec_items keeps an Arg's attrs (attrs_parsed), so it
# commutes with keeping the globals (global_comm) and with append.
def attrs_parsed(parsed: Cli.Usage, usage: String,
    +attrs: List<&2, Cli.Item>) ->
    {attrs == Cli.info_attrs(Cli.arg_info_parsed(parsed, usage, attrs))
      : List<&2, Cli.Item>}:
  match parsed:
    case Cli.Parsed{derived, short, long, kind}: {==}
    case Cli.Invalid{col}: {==}

# P holds for each list c may pick.
def item_pick(c: Bool, -P: List<&2, Cli.Item> -> Type, -a: List<&2, Cli.Item>,
    -b: List<&2, Cli.Item>, pa: P(a), pb: P(b)) ->
    P(Bool.pick(List<&2, Cli.Item>, c, a, b)):
  match c:
    case True{}: pa
    case False{}: pb

# A rule global_go may keep parses to one item, sr.
def spec_rule_pick(c: Bool, -r: Cli.Item, -rest: List<&2, Cli.Item>,
    -sr: Cli.SpecItem,
    e: {Cli.spec_items(r <> rest) == sr <> Cli.spec_items(rest)
      : List<&2, Cli.SpecItem>}) ->
    {Cli.spec_items(Bool.pick(List<&2, Cli.Item>, c, r <> rest, rest))
      == Bool.pick(List<&2, Cli.SpecItem>, c, sr <> Cli.spec_items(rest),
        Cli.spec_items(rest)) : List<&2, Cli.SpecItem>}:
  match c:
    case True{}: e
    case False{}: {==}

def global_pick(g: Bool, +usage: String, -help: String,
    +attrs: List<&2, Cli.Item>, +rest: List<&2, Cli.Item>) ->
    {Cli.spec_items(Bool.pick(List<&2, Cli.Item>, g,
      Cli.Arg{usage, help, attrs} <> rest, rest))
      == Bool.pick(List<&2, Cli.SpecItem>, g,
        Cli.SpecArg{Cli.arg_info(usage, attrs)} <> Cli.spec_items(rest),
        Cli.spec_items(rest)) : List<&2, Cli.SpecItem>}:
  match g:
    case True{}: {==}
    case False{}: {==}

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Arg --skip Exclusive --skip NeedOne cli.bend Item '$P <> tail' 'global_comm_go(tail, all)'
def global_comm_go(items: List<&2, Cli.Item>, +all: List<&2, Cli.Item>) ->
    {Cli.spec_items(Cli.global_go(items, all))
      == Cli.global_spec(Cli.spec_items(items), all)
      : List<&2, Cli.SpecItem>}:
  match items:
    case Nil{}: {==}
    case Cli.Arg{+usage, +help, +attrs} <> +tail:
      %global_comm_go(tail, all) :
        {Cli.spec_items(Bool.pick(List<&2, Cli.Item>, Cli.has_global(attrs),
          Cli.Arg{usage, help, attrs} <> Cli.global_go(tail, all),
          Cli.global_go(tail, all)))
          == Bool.pick(List<&2, Cli.SpecItem>,
            Cli.has_global(Cli.info_attrs(Cli.arg_info(usage, attrs))),
            Cli.SpecArg{Cli.arg_info(usage, attrs)} <> _, _)
          : List<&2, Cli.SpecItem>}
      %attrs_parsed(Cli.parse_usage(usage), usage, attrs) :
        {Cli.spec_items(Bool.pick(List<&2, Cli.Item>, Cli.has_global(attrs),
          Cli.Arg{usage, help, attrs} <> Cli.global_go(tail, all),
          Cli.global_go(tail, all)))
          == Bool.pick(List<&2, Cli.SpecItem>, Cli.has_global(_),
            Cli.SpecArg{Cli.arg_info(usage, attrs)}
              <> Cli.spec_items(Cli.global_go(tail, all)),
            Cli.spec_items(Cli.global_go(tail, all)))
          : List<&2, Cli.SpecItem>}
      global_pick(Cli.has_global(attrs), usage, help, attrs,
        Cli.global_go(tail, all))
    case Cli.Sub{x0, x1, x2} <> tail: global_comm_go(tail, all)
    case Cli.Version{x0} <> tail: global_comm_go(tail, all)
    case Cli.Alias{x0} <> tail: global_comm_go(tail, all)
    case Cli.Hidden{} <> tail: global_comm_go(tail, all)
    case Cli.Example{x0, x1} <> tail: global_comm_go(tail, all)
    case Cli.After{x0} <> tail: global_comm_go(tail, all)
    case Cli.SubOptional{} <> tail: global_comm_go(tail, all)
    case Cli.External{} <> tail: global_comm_go(tail, all)
    case Cli.Exclusive{+x0} <> +tail:
      %global_comm_go(tail, all) :
        {Cli.spec_items(Bool.pick(List<&2, Cli.Item>,
          Cli.group_global(all, x0),
          Cli.Exclusive{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all)))
          == Bool.pick(List<&2, Cli.SpecItem>,
            Cli.group_global(all, x0), Cli.SpecOther{Cli.Exclusive{x0}} <> _, _)
          : List<&2, Cli.SpecItem>}
      spec_rule_pick(Cli.group_global(all, x0), Cli.Exclusive{x0},
        Cli.global_go(tail, all), Cli.SpecOther{Cli.Exclusive{x0}}, {==})
    case Cli.NeedOne{+x0} <> +tail:
      %global_comm_go(tail, all) :
        {Cli.spec_items(Bool.pick(List<&2, Cli.Item>,
          Cli.group_global(all, x0),
          Cli.NeedOne{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all)))
          == Bool.pick(List<&2, Cli.SpecItem>,
            Cli.group_global(all, x0), Cli.SpecOther{Cli.NeedOne{x0}} <> _, _)
          : List<&2, Cli.SpecItem>}
      spec_rule_pick(Cli.group_global(all, x0), Cli.NeedOne{x0},
        Cli.global_go(tail, all), Cli.SpecOther{Cli.NeedOne{x0}}, {==})
    case Cli.Id{x0} <> tail: global_comm_go(tail, all)
    case Cli.Required{} <> tail: global_comm_go(tail, all)
    case Cli.AttrDefault{x0} <> tail: global_comm_go(tail, all)
    case Cli.AttrEnv{x0} <> tail: global_comm_go(tail, all)
    case Cli.Global{} <> tail: global_comm_go(tail, all)
    case Cli.Heading{x0} <> tail: global_comm_go(tail, all)
    case Cli.As{x0} <> tail: global_comm_go(tail, all)
    case Cli.OneOf{x0} <> tail: global_comm_go(tail, all)
    case Cli.Delim{x0} <> tail: global_comm_go(tail, all)
    case Cli.Hyphen{} <> tail: global_comm_go(tail, all)
    case Cli.Rest{} <> tail: global_comm_go(tail, all)
    case Cli.Bare{x0} <> tail: global_comm_go(tail, all)
    case Cli.Conflicts{x0} <> tail: global_comm_go(tail, all)
    case Cli.Requires{x0} <> tail: global_comm_go(tail, all)
    case Cli.Group{x0} <> tail: global_comm_go(tail, all)
    case Cli.Builtin{} <> tail: global_comm_go(tail, all)

def global_comm(+items: List<&2, Cli.Item>) ->
    {Cli.spec_items(Cli.global_items(items))
      == Cli.global_spec(Cli.spec_items(items), items)
      : List<&2, Cli.SpecItem>}:
  global_comm_go(items, items)

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Sub --skip Arg cli.bend Item '$P <> tail' '%spec_append(tail, ys) :\n  {Cli.SpecOther{$H}\n    <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),\n      Cli.spec_items(ys))\n    == Cli.SpecOther{$H} <> _ : List<&2, Cli.SpecItem>}\n{==}'
def spec_append(xs: List<&2, Cli.Item>, +ys: List<&2, Cli.Item>) ->
    {List.append(&2, Cli.SpecItem, Cli.spec_items(xs), Cli.spec_items(ys))
      == Cli.spec_items(List.append(&2, Cli.Item, xs, ys))
      : List<&2, Cli.SpecItem>}:
  match xs:
    case Nil{}: {==}
    case Cli.Sub{x0, x1, x2} <> tail: spec_append(tail, ys)
    case Cli.Arg{x0, x1, x2} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecArg{Cli.arg_info(x0, x2)}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecArg{Cli.arg_info(x0, x2)} <> _
          : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Version{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Version{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Version{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Alias{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Alias{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Alias{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Hidden{} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Hidden{}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Hidden{}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Example{x0, x1} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Example{x0, x1}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Example{x0, x1}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.After{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.After{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.After{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.SubOptional{} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.SubOptional{}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.SubOptional{}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.External{} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.External{}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.External{}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Exclusive{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Exclusive{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Exclusive{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.NeedOne{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.NeedOne{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.NeedOne{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Id{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Id{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Id{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Required{} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Required{}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Required{}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.AttrDefault{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.AttrDefault{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.AttrDefault{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.AttrEnv{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.AttrEnv{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.AttrEnv{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Global{} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Global{}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Global{}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Heading{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Heading{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Heading{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.As{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.As{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.As{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.OneOf{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.OneOf{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.OneOf{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Delim{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Delim{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Delim{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Hyphen{} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Hyphen{}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Hyphen{}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Rest{} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Rest{}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Rest{}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Bare{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Bare{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Bare{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Conflicts{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Conflicts{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Conflicts{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Requires{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Requires{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Requires{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Group{x0} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Group{x0}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Group{x0}} <> _ : List<&2, Cli.SpecItem>}
      {==}
    case Cli.Builtin{} <> tail:
      %spec_append(tail, ys) :
        {Cli.SpecOther{Cli.Builtin{}}
          <> List.append(&2, Cli.SpecItem, Cli.spec_items(tail),
            Cli.spec_items(ys))
          == Cli.SpecOther{Cli.Builtin{}} <> _ : List<&2, Cli.SpecItem>}
      {==}

def Laws.p19_inherit(items, globals):
  %global_comm(items) :
    {List.append(&2, Cli.SpecItem, _, Cli.spec_items(globals))
      == Cli.spec_items(List.append(&2, Cli.Item, Cli.global_items(items),
        globals)) : List<&2, Cli.SpecItem>}
  spec_append(Cli.global_items(items), globals)

# P19 sub: raw_subs keeps each Sub's name, aliases and children, and
# find_sub_key walks it as find_sub_go walks the items.
# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Alias cli.bend Item '$P <> tail' 'contains_aliases(tail, q)'
def contains_aliases(items: List<&2, Cli.Item>, +q: String) ->
    {Laws.aliases_name(items, q)
      == List.contains(~String, ~String.eq, Cli.find_aliases(items), q)
      : Bool}:
  match items:
    case Nil{}: {==}
    case Cli.Alias{name} <> +tail:
      %contains_cons(name, Cli.find_aliases(tail), q) :
        {Bool.or(String.eq(name, q), Laws.aliases_name(tail, q)) == _ : Bool}
      %contains_aliases(tail, q) :
        {Bool.or(String.eq(name, q), Laws.aliases_name(tail, q))
          == Bool.or(String.eq(name, q), _) : Bool}
      {==}
    case Cli.Arg{x0, x1, x2} <> tail: contains_aliases(tail, q)
    case Cli.Sub{x0, x1, x2} <> tail: contains_aliases(tail, q)
    case Cli.Version{x0} <> tail: contains_aliases(tail, q)
    case Cli.Hidden{} <> tail: contains_aliases(tail, q)
    case Cli.Example{x0, x1} <> tail: contains_aliases(tail, q)
    case Cli.After{x0} <> tail: contains_aliases(tail, q)
    case Cli.SubOptional{} <> tail: contains_aliases(tail, q)
    case Cli.External{} <> tail: contains_aliases(tail, q)
    case Cli.Exclusive{x0} <> tail: contains_aliases(tail, q)
    case Cli.NeedOne{x0} <> tail: contains_aliases(tail, q)
    case Cli.Id{x0} <> tail: contains_aliases(tail, q)
    case Cli.Required{} <> tail: contains_aliases(tail, q)
    case Cli.AttrDefault{x0} <> tail: contains_aliases(tail, q)
    case Cli.AttrEnv{x0} <> tail: contains_aliases(tail, q)
    case Cli.Global{} <> tail: contains_aliases(tail, q)
    case Cli.Heading{x0} <> tail: contains_aliases(tail, q)
    case Cli.As{x0} <> tail: contains_aliases(tail, q)
    case Cli.OneOf{x0} <> tail: contains_aliases(tail, q)
    case Cli.Delim{x0} <> tail: contains_aliases(tail, q)
    case Cli.Hyphen{} <> tail: contains_aliases(tail, q)
    case Cli.Rest{} <> tail: contains_aliases(tail, q)
    case Cli.Bare{x0} <> tail: contains_aliases(tail, q)
    case Cli.Conflicts{x0} <> tail: contains_aliases(tail, q)
    case Cli.Requires{x0} <> tail: contains_aliases(tail, q)
    case Cli.Group{x0} <> tail: contains_aliases(tail, q)
    case Cli.Builtin{} <> tail: contains_aliases(tail, q)

def sub_go_some(items: List<&2, Cli.Item>, +q: String, -h: Cli.SubFound) ->
    {Some{h} == Cli.find_sub_go(items, q, Some{h})
      : Maybe<&2, Cli.SubFound>}:
  match items:
    case Nil{}: {==}
    case head <> tail: {==}

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Sub cli.bend Item '$P <> tail' 'subkey_some(tail, q, k)'
def subkey_some(items: List<&2, Cli.Item>, +q: String, -k: Cli.SubKey) ->
    {Some{k} == Cli.find_sub_key(Cli.raw_subs(items), q, Some{k})
      : Maybe<&2, Cli.SubKey>}:
  match items:
    case Nil{}: {==}
    case Cli.Sub{x0, x1, x2} <> tail: {==}
    case Cli.Arg{x0, x1, x2} <> tail: subkey_some(tail, q, k)
    case Cli.Version{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Alias{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Hidden{} <> tail: subkey_some(tail, q, k)
    case Cli.Example{x0, x1} <> tail: subkey_some(tail, q, k)
    case Cli.After{x0} <> tail: subkey_some(tail, q, k)
    case Cli.SubOptional{} <> tail: subkey_some(tail, q, k)
    case Cli.External{} <> tail: subkey_some(tail, q, k)
    case Cli.Exclusive{x0} <> tail: subkey_some(tail, q, k)
    case Cli.NeedOne{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Id{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Required{} <> tail: subkey_some(tail, q, k)
    case Cli.AttrDefault{x0} <> tail: subkey_some(tail, q, k)
    case Cli.AttrEnv{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Global{} <> tail: subkey_some(tail, q, k)
    case Cli.Heading{x0} <> tail: subkey_some(tail, q, k)
    case Cli.As{x0} <> tail: subkey_some(tail, q, k)
    case Cli.OneOf{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Delim{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Hyphen{} <> tail: subkey_some(tail, q, k)
    case Cli.Rest{} <> tail: subkey_some(tail, q, k)
    case Cli.Bare{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Conflicts{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Requires{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Group{x0} <> tail: subkey_some(tail, q, k)
    case Cli.Builtin{} <> tail: subkey_some(tail, q, k)

def subkey_hit(-name: String, -children: List<&2, Cli.Item>,
    +tail: List<&2, Cli.Item>, +q: String) ->
    {Cli.find_sub_key(Cli.raw_subs(tail), q,
      Some{Cli.SubKey{name, Cli.find_aliases(children), children}})
      == Laws.sub_key_of(Cli.find_sub_go(tail, q,
        Some{Cli.SubFound{name, children}})) : Maybe<&2, Cli.SubKey>}:
  %subkey_some(tail, q,
    Cli.SubKey{name, Cli.find_aliases(children), children}) :
    {_ == Laws.sub_key_of(Cli.find_sub_go(tail, q,
      Some{Cli.SubFound{name, children}})) : Maybe<&2, Cli.SubKey>}
  %sub_go_some(tail, q, Cli.SubFound{name, children}) :
    {Some{Cli.SubKey{name, Cli.find_aliases(children), children}}
      == Laws.sub_key_of(_) : Maybe<&2, Cli.SubKey>}
  {==}

def subkey_alias(aliased: Bool, -name: String,
    -children: List<&2, Cli.Item>, +tail: List<&2, Cli.Item>, +q: String,
    ih: {Cli.find_sub_key(Cli.raw_subs(tail), q, None{})
      == Laws.sub_key_of(Cli.find_sub_go(tail, q, None{}))
      : Maybe<&2, Cli.SubKey>}) ->
    {Cli.find_sub_key(Cli.raw_subs(tail), q,
      Cli.sub_key_aliased(aliased, name, Cli.find_aliases(children),
        children))
      == Laws.sub_key_of(Cli.find_sub_go(tail, q,
        Cli.alias_hit(aliased, name, children))) : Maybe<&2, Cli.SubKey>}:
  match aliased:
    case True{}: subkey_hit(name, children, tail, q)
    case False{}: ih

def subkey_step(same: Bool, -name: String, +children: List<&2, Cli.Item>,
    +tail: List<&2, Cli.Item>, +q: String,
    ih: {Cli.find_sub_key(Cli.raw_subs(tail), q, None{})
      == Laws.sub_key_of(Cli.find_sub_go(tail, q, None{}))
      : Maybe<&2, Cli.SubKey>}) ->
    {Cli.find_sub_key(Cli.raw_subs(tail), q,
      Cli.sub_key_hit(same, name, Cli.find_aliases(children), children, q))
      == Laws.sub_key_of(Cli.find_sub_go(tail, q,
        Cli.sub_hit(same, name, children, q))) : Maybe<&2, Cli.SubKey>}:
  match same:
    case True{}: subkey_hit(name, children, tail, q)
    case False{}:
      %contains_aliases(children, q) :
        {Cli.find_sub_key(Cli.raw_subs(tail), q,
          Cli.sub_key_aliased(_, name, Cli.find_aliases(children), children))
          == Laws.sub_key_of(Cli.find_sub_go(tail, q,
            Cli.alias_hit(Cli.has_alias(children, q, False{}), name,
              children))) : Maybe<&2, Cli.SubKey>}
      %alias_go(children, q, False{}) :
        {Cli.find_sub_key(Cli.raw_subs(tail), q,
          Cli.sub_key_aliased(Laws.aliases_name(children, q), name,
            Cli.find_aliases(children), children))
          == Laws.sub_key_of(Cli.find_sub_go(tail, q,
            Cli.alias_hit(_, name, children))) : Maybe<&2, Cli.SubKey>}
      subkey_alias(Laws.aliases_name(children, q), name, children, tail, q,
        ih)

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Sub cli.bend Item '$P <> tail' 'subkey_go(tail, q)'
def subkey_go(items: List<&2, Cli.Item>, +q: String) ->
    {Cli.find_sub_key(Cli.raw_subs(items), q, None{})
      == Laws.sub_key_of(Cli.find_sub_go(items, q, None{}))
      : Maybe<&2, Cli.SubKey>}:
  match items:
    case Nil{}: {==}
    case Cli.Sub{+name, about, +children} <> +tail:
      subkey_step(Cli.same_text(q, name), name, children, tail, q,
        subkey_go(tail, q))
    case Cli.Arg{x0, x1, x2} <> tail: subkey_go(tail, q)
    case Cli.Version{x0} <> tail: subkey_go(tail, q)
    case Cli.Alias{x0} <> tail: subkey_go(tail, q)
    case Cli.Hidden{} <> tail: subkey_go(tail, q)
    case Cli.Example{x0, x1} <> tail: subkey_go(tail, q)
    case Cli.After{x0} <> tail: subkey_go(tail, q)
    case Cli.SubOptional{} <> tail: subkey_go(tail, q)
    case Cli.External{} <> tail: subkey_go(tail, q)
    case Cli.Exclusive{x0} <> tail: subkey_go(tail, q)
    case Cli.NeedOne{x0} <> tail: subkey_go(tail, q)
    case Cli.Id{x0} <> tail: subkey_go(tail, q)
    case Cli.Required{} <> tail: subkey_go(tail, q)
    case Cli.AttrDefault{x0} <> tail: subkey_go(tail, q)
    case Cli.AttrEnv{x0} <> tail: subkey_go(tail, q)
    case Cli.Global{} <> tail: subkey_go(tail, q)
    case Cli.Heading{x0} <> tail: subkey_go(tail, q)
    case Cli.As{x0} <> tail: subkey_go(tail, q)
    case Cli.OneOf{x0} <> tail: subkey_go(tail, q)
    case Cli.Delim{x0} <> tail: subkey_go(tail, q)
    case Cli.Hyphen{} <> tail: subkey_go(tail, q)
    case Cli.Rest{} <> tail: subkey_go(tail, q)
    case Cli.Bare{x0} <> tail: subkey_go(tail, q)
    case Cli.Conflicts{x0} <> tail: subkey_go(tail, q)
    case Cli.Requires{x0} <> tail: subkey_go(tail, q)
    case Cli.Group{x0} <> tail: subkey_go(tail, q)
    case Cli.Builtin{} <> tail: subkey_go(tail, q)

def Laws.p19_sub(items, globals, path, query):
  subkey_go(items, query)

# String.eq(a, b) holds only of a == b, through same_go, Char.is_eq and
# Word.cmp; so String.eq is symmetric (str_sym).

def cmp_disc(c: Cmp) -> Data:
  match c:
    case EQ{}: Empty
    case LT{}: Unit
    case GT{}: Unit

def lt_eq_absurd(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : cmp_disc(_)
  Unit{}

def gt_eq_absurd(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : cmp_disc(_)
  Unit{}

def bool_cmp_eq(a: Bool, b: Bool, e: {Bool.cmp(a, b) == EQ{} : Cmp}) ->
    {a == b : Bool}:
  match a b:
    case False{} False{}: {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, lt_eq_absurd(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, gt_eq_absurd(e))
    case True{} True{}: {==}

def fin_eq_rest(ab: Bool, bb: Bool, t: Cmp,
    e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}: Empty.absurd({LT{} == EQ{} : Cmp}, lt_eq_absurd(e))
    case EQ{}: {==}
    case GT{}: Empty.absurd({GT{} == EQ{} : Cmp}, gt_eq_absurd(e))

def fin_eq_bool(ab: Bool, bb: Bool, t: Cmp,
    e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {ab == bb : Bool}:
  match t:
    case LT{}: Empty.absurd({ab == bb : Bool}, lt_eq_absurd(e))
    case EQ{}: bool_cmp_eq(ab, bb, e)
    case GT{}: Empty.absurd({ab == bb : Bool}, gt_eq_absurd(e))

def word_reflect(n: Nat, a: Word(n), b: Word(n),
    +e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}: {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %word_reflect(p, at, bt,
            fin_eq_rest(ab, bb, Word.cmp(p, at, bt), e)) :
            {WCon{ab, at} == WCon{bb, _} : Word(1n+p)}
          %fin_eq_bool(ab, bb, Word.cmp(p, at, bt), e) :
            {WCon{ab, at} == WCon{_, at} : Word(1n+p)}
          {==}

def is_eq_true(c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) ->
    {c == EQ{} : Cmp}:
  match c:
    case EQ{}: {==}
    case LT{}: Empty.absurd({LT{} == EQ{} : Cmp}, false_true_absurd(e))
    case GT{}: Empty.absurd({GT{} == EQ{} : Cmp}, false_true_absurd(e))

def char_reflect(x: Char, y: Char,
    e: {Char.is_eq(x, y) == True{} : Bool}) -> {x == y : Char}:
  match x y:
    case Chr{U32{+a}} Chr{U32{+b}}:
      %word_reflect(32n, a, b, is_eq_true(Word.cmp(32n, a, b), e)) :
        {Chr{U32{a}} == Chr{U32{_}} : Char}
      {==}

def same_flag(xt: String, yt: String, c: Bool,
    e: {Cli.same_go(xt, yt, c) == True{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}: {==}
    case False{}:
      %same_go_false(xt, yt) : {_ == True{} : Bool}
      e

def same_rest(+xt: String, +yt: String, c: Bool,
    e: {Cli.same_go(xt, yt, c) == True{} : Bool}) ->
    {Cli.same_go(xt, yt, True{}) == True{} : Bool}:
  match c:
    case True{}: e
    case False{}:
      Empty.absurd({Cli.same_go(xt, yt, True{}) == True{} : Bool},
        false_true_absurd(same_flag(xt, yt, False{}, e)))

def same_reflect(a: String, b: String,
    +e: {Cli.same_go(a, b, True{}) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{h, t}:
      Empty.absurd({SNil{} == SCon{h, t} : String}, false_true_absurd(e))
    case SCon{h, t} SNil{}:
      Empty.absurd({SCon{h, t} == SNil{} : String}, false_true_absurd(e))
    case SCon{+x, +xt} SCon{+y, +yt}:
      %same_reflect(xt, yt, same_rest(xt, yt, Char.is_eq(x, y), e)) :
        {SCon{x, xt} == SCon{y, _} : String}
      %char_reflect(x, y, same_flag(xt, yt, Char.is_eq(x, y), e)) :
        {SCon{x, xt} == SCon{_, xt} : String}
      {==}

def eq_reflect(+a: String, +b: String,
    e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  same_reflect(a, b, Equal.trans(Bool, Cli.same_text(a, b), String.eq(a, b),
    True{}, Laws.p18_text(a, b), e))

def eq_sym_by(c: Bool, d: Bool, +a: String, +b: String,
    ec: {String.eq(a, b) == c : Bool}, ed: {String.eq(b, a) == d : Bool}) ->
    {c == d : Bool}:
  match c d:
    case True{} True{}: {==}
    case False{} False{}: {==}
    case True{} False{}:
      %ed : {True{} == _ : Bool}
      %eq_reflect(a, b, ec) : {True{} == String.eq(_, a) : Bool}
      %string_eq_refl(a) : {_ == String.eq(a, a) : Bool}
      {==}
    case False{} True{}:
      %ec : {_ == True{} : Bool}
      %eq_reflect(b, a, ed) : {String.eq(_, b) == True{} : Bool}
      string_eq_refl(b)

def str_sym(+a: String, +b: String) ->
    {String.eq(a, b) == String.eq(b, a) : Bool}:
  eq_sym_by(String.eq(a, b), String.eq(b, a), a, b, {==}, {==})

# P19 option: find_option tries each Arg's names in turn and computes the
# polarity from the query, while spec_keys makes a key per name with the
# polarity from the key's name. The two agree where the names are equal
# (name_hit), and the key list is the names' lists appended (contains4).

def findkey_some(keys: List<&2, Cli.OptKey>, +q: String,
    -h: Cli.OptFound) ->
    {Some{h} == Cli.find_key(keys, q, Some{h}) : Maybe<&2, Cli.OptFound>}:
  match keys:
    case Nil{}: {==}
    case k <> t: {==}

def findkey_append(xs: List<&2, Cli.OptKey>, +ys: List<&2, Cli.OptKey>,
    +q: String, found: Maybe<&2, Cli.OptFound>) ->
    {Maybe.or(&2, Cli.OptFound, Cli.find_key(xs, q, found),
      Cli.find_key(ys, q, None{}))
      == Cli.find_key(List.append(&2, Cli.OptKey, xs, ys), q, found)
      : Maybe<&2, Cli.OptFound>}:
  match xs found:
    case Nil{} None{}: {==}
    case Nil{} Some{h}: findkey_some(ys, q, h)
    case k <> t Some{h}: {==}
    case k <> t None{}: findkey_append(t, ys, q, Cli.key_found(k, q))

# A key's polarity, as opt_key computes it from the key's name.
def pol(+name: String, info: Cli.ArgInfo) -> Bool:
  match info:
    case Cli.ArgInfo{id, usage, short, +long, kind, attrs}:
      Bool.not(Bool.and(Cli.kind_negatable(kind),
        Bool.and(Bool.not(String.is_empty(long)),
          String.eq(name, Cli.negated_long(long)))))

def opt_key_eq(+name: String, info: Cli.ArgInfo) ->
    {Cli.OptKey{name, Cli.OptFound{info, pol(name, info)}}
      == Cli.opt_key(name, info) : Cli.OptKey}:
  match info:
    case Cli.ArgInfo{id, usage, short, long, kind, attrs}: {==}

def name_hit(s: Bool, +q: String, +n: String, -info: Cli.ArgInfo,
    -c: Bool, e: {Cli.same_text(q, n) == s : Bool}) ->
    {Bool.pick(Maybe<&2, Cli.OptFound>, Bool.or(s, c),
      Some{Cli.OptFound{info, pol(q, info)}}, None{})
      == Maybe.or(&2, Cli.OptFound,
        Bool.pick(Maybe<&2, Cli.OptFound>, s,
          Some{Cli.OptFound{info, pol(n, info)}}, None{}),
        Bool.pick(Maybe<&2, Cli.OptFound>, c,
          Some{Cli.OptFound{info, pol(q, info)}}, None{}))
      : Maybe<&2, Cli.OptFound>}:
  match s:
    case True{}:
      %same_reflect(q, n, e) :
        {Some{Cli.OptFound{info, pol(q, info)}}
          == Some{Cli.OptFound{info, pol(_, info)}}
          : Maybe<&2, Cli.OptFound>}
      {==}
    case False{}: {==}

def names_go(ns: List<&2, String>, +q: String, +info: Cli.ArgInfo,
    found: Maybe<&2, Cli.OptFound>) ->
    {Maybe.or(&2, Cli.OptFound, found,
      Bool.pick(Maybe<&2, Cli.OptFound>,
        List.contains(~String, ~String.eq, ns, q),
        Some{Cli.OptFound{info, pol(q, info)}}, None{}))
      == Cli.find_key(Cli.name_keys(ns, info), q, found)
      : Maybe<&2, Cli.OptFound>}:
  match ns found:
    case Nil{} None{}: {==}
    case Nil{} Some{h}: {==}
    case n <> t Some{h}: {==}
    case +n <> +t None{}:
      %contains_cons(n, t, q) :
        {Bool.pick(Maybe<&2, Cli.OptFound>, _,
          Some{Cli.OptFound{info, pol(q, info)}}, None{})
          == Cli.find_key(Cli.name_keys(t, info), q,
            Cli.key_found(Cli.opt_key(n, info), q))
          : Maybe<&2, Cli.OptFound>}
      %names_go(t, q, info, Cli.key_found(Cli.opt_key(n, info), q)) :
        {Bool.pick(Maybe<&2, Cli.OptFound>,
          Bool.or(String.eq(n, q), List.contains(~String, ~String.eq, t, q)),
          Some{Cli.OptFound{info, pol(q, info)}}, None{}) == _
          : Maybe<&2, Cli.OptFound>}
      %opt_key_eq(n, info) :
        {Bool.pick(Maybe<&2, Cli.OptFound>,
          Bool.or(String.eq(n, q), List.contains(~String, ~String.eq, t, q)),
          Some{Cli.OptFound{info, pol(q, info)}}, None{})
          == Maybe.or(&2, Cli.OptFound, Cli.key_found(_, q),
            Bool.pick(Maybe<&2, Cli.OptFound>,
              List.contains(~String, ~String.eq, t, q),
              Some{Cli.OptFound{info, pol(q, info)}}, None{}))
          : Maybe<&2, Cli.OptFound>}
      %str_sym(q, n) :
        {Bool.pick(Maybe<&2, Cli.OptFound>,
          Bool.or(_, List.contains(~String, ~String.eq, t, q)),
          Some{Cli.OptFound{info, pol(q, info)}}, None{})
          == Maybe.or(&2, Cli.OptFound,
            Bool.pick(Maybe<&2, Cli.OptFound>, Cli.same_text(q, n),
              Some{Cli.OptFound{info, pol(n, info)}}, None{}),
            Bool.pick(Maybe<&2, Cli.OptFound>,
              List.contains(~String, ~String.eq, t, q),
              Some{Cli.OptFound{info, pol(q, info)}}, None{}))
          : Maybe<&2, Cli.OptFound>}
      %Laws.p18_text(q, n) :
        {Bool.pick(Maybe<&2, Cli.OptFound>,
          Bool.or(_, List.contains(~String, ~String.eq, t, q)),
          Some{Cli.OptFound{info, pol(q, info)}}, None{})
          == Maybe.or(&2, Cli.OptFound,
            Bool.pick(Maybe<&2, Cli.OptFound>, Cli.same_text(q, n),
              Some{Cli.OptFound{info, pol(n, info)}}, None{}),
            Bool.pick(Maybe<&2, Cli.OptFound>,
              List.contains(~String, ~String.eq, t, q),
              Some{Cli.OptFound{info, pol(q, info)}}, None{}))
          : Maybe<&2, Cli.OptFound>}
      name_hit(Cli.same_text(q, n), q, n, info,
        List.contains(~String, ~String.eq, t, q), {==})

def or_assoc(a: Bool, b: Bool, c: Bool) ->
    {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}: {==}
    case False{}: {==}

def contains_append(xs: List<&2, String>, +ys: List<&2, String>,
    +q: String) ->
    {Bool.or(List.contains(~String, ~String.eq, xs, q),
      List.contains(~String, ~String.eq, ys, q))
      == List.contains(~String, ~String.eq,
        List.append(&2, String, xs, ys), q) : Bool}:
  match xs:
    case Nil{}: {==}
    case +x <> +t:
      %contains_cons(x, t, q) :
        {Bool.or(_, List.contains(~String, ~String.eq, ys, q))
          == List.contains(~String, ~String.eq,
            x <> List.append(&2, String, t, ys), q) : Bool}
      %contains_cons(x, List.append(&2, String, t, ys), q) :
        {Bool.or(Bool.or(String.eq(x, q),
          List.contains(~String, ~String.eq, t, q)),
          List.contains(~String, ~String.eq, ys, q)) == _ : Bool}
      %contains_append(t, ys, q) :
        {Bool.or(Bool.or(String.eq(x, q),
          List.contains(~String, ~String.eq, t, q)),
          List.contains(~String, ~String.eq, ys, q))
          == Bool.or(String.eq(x, q), _) : Bool}
      or_assoc(String.eq(x, q), List.contains(~String, ~String.eq, t, q),
        List.contains(~String, ~String.eq, ys, q))

def any_last(x: Bool) -> {x == List.any.if(u => False{}, x) : Bool}:
  match x:
    case True{}: {==}
    case False{}: {==}

def sym_contains_one(+q: String, +s: String) ->
    {String.eq(q, s) == List.contains(~String, ~String.eq, [s], q) : Bool}:
  %str_sym(s, q) : {_ == List.any.if(u => False{}, String.eq(s, q)) : Bool}
  any_last(String.eq(s, q))

def nonempty_contains(s: String, +q: String) ->
    {Bool.and(Bool.not(String.is_empty(s)), String.eq(q, s))
      == List.contains(~String, ~String.eq, Cli.nonempty_name(s), q)
      : Bool}:
  match s:
    case SNil{}: {==}
    case SCon{+h, +t}: sym_contains_one(q, SCon{h, t})

def neg_contains(g: Bool, l: Bool, +nl: String, +q: String) ->
    {Bool.and(g, Bool.and(l, String.eq(q, nl)))
      == List.contains(~String, ~String.eq,
        Bool.pick(List<&2, String>, Bool.and(g, l), [nl], []), q) : Bool}:
  match g l:
    case True{} True{}: sym_contains_one(q, nl)
    case True{} False{}: {==}
    case False{} _: {==}

def or4(a: Bool, b: Bool, c: Bool, d: Bool) ->
    {Bool.or(Bool.or(a, Bool.or(b, c)), d)
      == Bool.or(a, Bool.or(b, Bool.or(c, d))) : Bool}:
  match a b:
    case True{} _: {==}
    case False{} True{}: {==}
    case False{} False{}: {==}

def contains4(xa: List<&2, String>, +xb: List<&2, String>,
    +xc: List<&2, String>, +xd: List<&2, String>, +q: String) ->
    {Bool.or(List.contains(~String, ~String.eq, xa, q),
      Bool.or(List.contains(~String, ~String.eq, xb, q),
        Bool.or(List.contains(~String, ~String.eq, xc, q),
          List.contains(~String, ~String.eq, xd, q))))
      == List.contains(~String, ~String.eq,
        List.append(&2, String, xa, List.append(&2, String, xb,
          List.append(&2, String, xc, xd))), q) : Bool}:
  %contains_append(xa, List.append(&2, String, xb,
    List.append(&2, String, xc, xd)), q) :
    {Bool.or(List.contains(~String, ~String.eq, xa, q),
      Bool.or(List.contains(~String, ~String.eq, xb, q),
        Bool.or(List.contains(~String, ~String.eq, xc, q),
          List.contains(~String, ~String.eq, xd, q)))) == _ : Bool}
  %contains_append(xb, List.append(&2, String, xc, xd), q) :
    {Bool.or(List.contains(~String, ~String.eq, xa, q),
      Bool.or(List.contains(~String, ~String.eq, xb, q),
        Bool.or(List.contains(~String, ~String.eq, xc, q),
          List.contains(~String, ~String.eq, xd, q))))
      == Bool.or(List.contains(~String, ~String.eq, xa, q), _) : Bool}
  %contains_append(xc, xd, q) :
    {Bool.or(List.contains(~String, ~String.eq, xa, q),
      Bool.or(List.contains(~String, ~String.eq, xb, q),
        Bool.or(List.contains(~String, ~String.eq, xc, q),
          List.contains(~String, ~String.eq, xd, q))))
      == Bool.or(List.contains(~String, ~String.eq, xa, q),
        Bool.or(List.contains(~String, ~String.eq, xb, q), _)) : Bool}
  {==}

def matches_names(info: Cli.ArgInfo, +q: String) ->
    {Cli.option_matches(q, info)
      == Bool.pick(Maybe<&2, Cli.OptFound>,
        List.contains(~String, ~String.eq, Cli.info_names(info), q),
        Some{Cli.OptFound{info, pol(q, info)}}, None{})
      : Maybe<&2, Cli.OptFound>}:
  match info:
    case Cli.ArgInfo{id, usage, +short, +long, +kind, +attrs}:
      %contains4(Cli.nonempty_name(short), Cli.nonempty_name(long),
        Cli.find_aliases(attrs),
        Bool.pick(List<&2, String>, Bool.and(Cli.kind_negatable(kind),
          Bool.not(String.is_empty(long))), [Cli.negated_long(long)], []),
        q) :
        {Cli.option_matches(q, Cli.ArgInfo{id, usage, short, long, kind,
          attrs}) == Bool.pick(Maybe<&2, Cli.OptFound>, _,
            Some{Cli.OptFound{Cli.ArgInfo{id, usage, short, long, kind,
              attrs}, pol(q, Cli.ArgInfo{id, usage, short, long, kind,
                attrs})}}, None{}) : Maybe<&2, Cli.OptFound>}
      %nonempty_contains(short, q) :
        {Cli.option_matches(q, Cli.ArgInfo{id, usage, short, long, kind,
          attrs}) == Bool.pick(Maybe<&2, Cli.OptFound>,
            Bool.or(_, Bool.or(List.contains(~String, ~String.eq,
              Cli.nonempty_name(long), q),
              Bool.or(List.contains(~String, ~String.eq,
                Cli.find_aliases(attrs), q),
                List.contains(~String, ~String.eq,
                  Bool.pick(List<&2, String>,
                    Bool.and(Cli.kind_negatable(kind),
                      Bool.not(String.is_empty(long))),
                    [Cli.negated_long(long)], []), q)))),
            Some{Cli.OptFound{Cli.ArgInfo{id, usage, short, long, kind,
              attrs}, pol(q, Cli.ArgInfo{id, usage, short, long, kind,
                attrs})}}, None{}) : Maybe<&2, Cli.OptFound>}
      %nonempty_contains(long, q) :
        {Cli.option_matches(q, Cli.ArgInfo{id, usage, short, long, kind,
          attrs}) == Bool.pick(Maybe<&2, Cli.OptFound>,
            Bool.or(Bool.and(Bool.not(String.is_empty(short)),
              String.eq(q, short)), Bool.or(_,
              Bool.or(List.contains(~String, ~String.eq,
                Cli.find_aliases(attrs), q),
                List.contains(~String, ~String.eq,
                  Bool.pick(List<&2, String>,
                    Bool.and(Cli.kind_negatable(kind),
                      Bool.not(String.is_empty(long))),
                    [Cli.negated_long(long)], []), q)))),
            Some{Cli.OptFound{Cli.ArgInfo{id, usage, short, long, kind,
              attrs}, pol(q, Cli.ArgInfo{id, usage, short, long, kind,
                attrs})}}, None{}) : Maybe<&2, Cli.OptFound>}
      %neg_contains(Cli.kind_negatable(kind),
        Bool.not(String.is_empty(long)), Cli.negated_long(long), q) :
        {Cli.option_matches(q, Cli.ArgInfo{id, usage, short, long, kind,
          attrs}) == Bool.pick(Maybe<&2, Cli.OptFound>,
            Bool.or(Bool.and(Bool.not(String.is_empty(short)),
              String.eq(q, short)),
              Bool.or(Bool.and(Bool.not(String.is_empty(long)),
                String.eq(q, long)),
                Bool.or(List.contains(~String, ~String.eq,
                  Cli.find_aliases(attrs), q), _))),
            Some{Cli.OptFound{Cli.ArgInfo{id, usage, short, long, kind,
              attrs}, pol(q, Cli.ArgInfo{id, usage, short, long, kind,
                attrs})}}, None{}) : Maybe<&2, Cli.OptFound>}
      %or4(Bool.and(Bool.not(String.is_empty(short)), String.eq(q, short)),
        Bool.and(Bool.not(String.is_empty(long)), String.eq(q, long)),
        List.contains(~String, ~String.eq, Cli.find_aliases(attrs), q),
        Bool.and(Cli.kind_negatable(kind),
          Bool.and(Bool.not(String.is_empty(long)),
            String.eq(q, Cli.negated_long(long))))) :
        {Cli.option_matches(q, Cli.ArgInfo{id, usage, short, long, kind,
          attrs}) == Bool.pick(Maybe<&2, Cli.OptFound>, _,
            Some{Cli.OptFound{Cli.ArgInfo{id, usage, short, long, kind,
              attrs}, pol(q, Cli.ArgInfo{id, usage, short, long, kind,
                attrs})}}, None{}) : Maybe<&2, Cli.OptFound>}
      {==}

def or_pick(m: Maybe<&2, Cli.OptFound>, -rest: Maybe<&2, Cli.OptFound>) ->
    {Bool.pick(Maybe<&2, Cli.OptFound>, Maybe.is_some(&2, Cli.OptFound, m),
      m, rest) == Maybe.or(&2, Cli.OptFound, m, rest)
      : Maybe<&2, Cli.OptFound>}:
  match m:
    case None{}: {==}
    case Some{x}: {==}

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Arg cli.bend Item '$P <> tail' 'option_go(tail, q)'
def option_go(items: List<&2, Cli.Item>, +q: String) ->
    {Cli.find_option(items, q)
      == Cli.find_key(Cli.spec_keys(Cli.spec_items(items)), q, None{})
      : Maybe<&2, Cli.OptFound>}:
  match items:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      %findkey_append(Cli.name_keys(Cli.info_names(Cli.arg_info(usage,
        attrs)), Cli.arg_info(usage, attrs)),
        Cli.spec_keys(Cli.spec_items(tail)), q, None{}) :
        {Cli.find_option(Cli.Arg{usage, help, attrs} <> tail, q) == _
          : Maybe<&2, Cli.OptFound>}
      %option_go(tail, q) :
        {Cli.find_option(Cli.Arg{usage, help, attrs} <> tail, q)
          == Maybe.or(&2, Cli.OptFound,
            Cli.find_key(Cli.name_keys(Cli.info_names(Cli.arg_info(usage,
              attrs)), Cli.arg_info(usage, attrs)), q, None{}), _)
          : Maybe<&2, Cli.OptFound>}
      %names_go(Cli.info_names(Cli.arg_info(usage, attrs)), q,
        Cli.arg_info(usage, attrs), None{}) :
        {Cli.find_option(Cli.Arg{usage, help, attrs} <> tail, q)
          == Maybe.or(&2, Cli.OptFound, _, Cli.find_option(tail, q))
          : Maybe<&2, Cli.OptFound>}
      %matches_names(Cli.arg_info(usage, attrs), q) :
        {Cli.find_option(Cli.Arg{usage, help, attrs} <> tail, q)
          == Maybe.or(&2, Cli.OptFound, _, Cli.find_option(tail, q))
          : Maybe<&2, Cli.OptFound>}
      or_pick(Cli.option_matches(q, Cli.arg_info(usage, attrs)),
        Cli.find_option(tail, q))
    case Cli.Sub{x0, x1, x2} <> tail: option_go(tail, q)
    case Cli.Version{x0} <> tail: option_go(tail, q)
    case Cli.Alias{x0} <> tail: option_go(tail, q)
    case Cli.Hidden{} <> tail: option_go(tail, q)
    case Cli.Example{x0, x1} <> tail: option_go(tail, q)
    case Cli.After{x0} <> tail: option_go(tail, q)
    case Cli.SubOptional{} <> tail: option_go(tail, q)
    case Cli.External{} <> tail: option_go(tail, q)
    case Cli.Exclusive{x0} <> tail: option_go(tail, q)
    case Cli.NeedOne{x0} <> tail: option_go(tail, q)
    case Cli.Id{x0} <> tail: option_go(tail, q)
    case Cli.Required{} <> tail: option_go(tail, q)
    case Cli.AttrDefault{x0} <> tail: option_go(tail, q)
    case Cli.AttrEnv{x0} <> tail: option_go(tail, q)
    case Cli.Global{} <> tail: option_go(tail, q)
    case Cli.Heading{x0} <> tail: option_go(tail, q)
    case Cli.As{x0} <> tail: option_go(tail, q)
    case Cli.OneOf{x0} <> tail: option_go(tail, q)
    case Cli.Delim{x0} <> tail: option_go(tail, q)
    case Cli.Hyphen{} <> tail: option_go(tail, q)
    case Cli.Rest{} <> tail: option_go(tail, q)
    case Cli.Bare{x0} <> tail: option_go(tail, q)
    case Cli.Conflicts{x0} <> tail: option_go(tail, q)
    case Cli.Requires{x0} <> tail: option_go(tail, q)
    case Cli.Group{x0} <> tail: option_go(tail, q)
    case Cli.Builtin{} <> tail: option_go(tail, q)

def Laws.p19_option(items, globals, path, query):
  %findkey_append(Cli.spec_keys(Cli.spec_items(items)),
    Cli.spec_keys(Cli.spec_items(globals)), query, None{}) :
    {_ == Maybe.or(&2, Cli.OptFound, Cli.find_option(items, query),
      Cli.find_option(globals, query)) : Maybe<&2, Cli.OptFound>}
  %option_go(items, query) :
    {Maybe.or(&2, Cli.OptFound, _,
      Cli.find_key(Cli.spec_keys(Cli.spec_items(globals)), query, None{}))
      == Maybe.or(&2, Cli.OptFound, Cli.find_option(items, query),
        Cli.find_option(globals, query)) : Maybe<&2, Cli.OptFound>}
  %option_go(globals, query) :
    {Maybe.or(&2, Cli.OptFound, Cli.find_option(items, query), _)
      == Maybe.or(&2, Cli.OptFound, Cli.find_option(items, query),
        Cli.find_option(globals, query)) : Maybe<&2, Cli.OptFound>}
  {==}

# P19 verdict: scope_walk follows the path down the scan's scopes and
# scope_args' globals together, generalised over the globals inherited so
# far; at each name, p19_sub makes both walks take the same subcommand and
# p19_inherit gives its scope those globals. At the path's end, spec_append
# and p19_arg make the scanner's lookup find_arg_info's.

# Past a name with no subcommand, scope_at stays None.
def none_at(path: List<&2, String>) ->
    {None{} == Laws.scope_at(path, None{}) : Maybe<&2, Cli.Scope>}:
  match path:
    case Nil{}: {==}
    case name <> tail: {==}

# What the scanner's lookup finds in scope, when there is one, against what
# find_arg_info finds among args.
def ScopeFound(scope: Maybe<&2, Cli.Scope>, args: List<&2, Cli.Item>,
    id: String) -> Type:
  match scope:
    case None{}: Unit
    case Some{s}:
      {Cli.find_spec_info(Cli.scope_arg_items(s), id, None{})
        == Cli.find_arg_info(args, id) : Maybe<&2, Cli.ArgInfo>}

def scope_end(+items: List<&2, Cli.Item>, +globals: List<&2, Cli.Item>,
    -p: List<&2, String>, id: String) ->
    ScopeFound(Some{Cli.Scope{p,
        Cli.spec_node(items, Cli.spec_items(globals))}},
      Cli.scope_args([], items, globals), id):
  %Equal.sym(List<&2, Cli.SpecItem>,
      List.append(&2, Cli.SpecItem, Cli.spec_items(globals),
        Cli.spec_items(items)),
      Cli.spec_items(List.append(&2, Cli.Item, globals, items)),
      spec_append(globals, items)) :
    {Cli.find_spec_info(_, id, None{})
      == Cli.find_arg_info(List.append(&2, Cli.Item, globals, items), id)
      : Maybe<&2, Cli.ArgInfo>}
  Laws.p19_arg(List.append(&2, Cli.Item, globals, items), id)

def scope_step(found: Maybe<&2, Cli.SubFound>, tail: List<&2, String>,
    items: List<&2, Cli.Item>, globals: List<&2, Cli.Item>,
    p: List<&2, String>, -events: List<&2, Cli.ScanEvent>, -resting: Bool,
    -count: Nat, -external: Maybe<&2, Cli.ExternalArgs>,
    -issue: Maybe<&2, Cli.ScanFault>, -id: String,
    ih: @p2: List<&2, String> -> @-ev2: List<&2, Cli.ScanEvent> ->
      @kids: List<&2, Cli.Item> ->
      ScopeFound(Laws.scope_at(tail, Some{Cli.ScanState{Cli.Scope{p2,
          Cli.spec_node(kids, Cli.spec_items(List.append(&2, Cli.Item,
            Cli.global_items(items), globals)))}, ev2, resting, 0n, external,
          issue}}),
        Cli.scope_args(tail, kids, List.append(&2, Cli.Item,
          Cli.global_items(items), globals)), id)) ->
    ScopeFound(Laws.scope_at(tail, Laws.scan_enter(Laws.sub_key_of(found),
        Cli.ScanState{Cli.Scope{p,
          Cli.spec_node(items, Cli.spec_items(globals))}, events, resting,
          count, external, issue})),
      Cli.scope_args(tail, Cli.sub_items(found), List.append(&2, Cli.Item,
        Cli.global_items(items), globals)), id):
  match found:
    case None{}:
      %none_at(tail) : ScopeFound(_, Cli.scope_args(tail, [],
        List.append(&2, Cli.Item, Cli.global_items(items), globals)), id)
      Unit{}
    case Some{Cli.SubFound{name, children}}:
      %Equal.sym(List<&2, Cli.SpecItem>,
          Cli.spec_inherit(Cli.spec_node(items, Cli.spec_items(globals))),
          Cli.spec_items(List.append(&2, Cli.Item, Cli.global_items(items),
            globals)), Laws.p19_inherit(items, globals)) :
        ScopeFound(Laws.scope_at(tail,
          Some{Cli.ScanState{Cli.Scope{List.append(&2, String, p, [name]),
            Cli.spec_node(children, _)},
            Cli.Enter{name} <> Cli.events_inherited(events, _), resting,
            0n, external, issue}}),
        Cli.scope_args(tail, children, List.append(&2, Cli.Item,
          Cli.global_items(items), globals)), id)
      ih(List.append(&2, String, p, [name]),
        Cli.Enter{name} <> Cli.events_inherited(events,
          Cli.spec_items(List.append(&2, Cli.Item, Cli.global_items(items),
            globals))), children)

def scope_walk(path: List<&2, String>, +items: List<&2, Cli.Item>,
    +globals: List<&2, Cli.Item>, +p: List<&2, String>,
    -events: List<&2, Cli.ScanEvent>, -resting: Bool, -count: Nat,
    -external: Maybe<&2, Cli.ExternalArgs>, -issue: Maybe<&2, Cli.ScanFault>,
    +id: String) ->
    ScopeFound(Laws.scope_at(path, Some{Cli.ScanState{Cli.Scope{p,
        Cli.spec_node(items, Cli.spec_items(globals))}, events, resting, count,
        external, issue}}), Cli.scope_args(path, items, globals), id):
  match path:
    case Nil{}: scope_end(items, globals, p, id)
    case +name <> +tail:
      %Equal.sym(Maybe<&2, Cli.SubKey>,
          Cli.scope_find_sub(Cli.Scope{p, Cli.spec_node(items,
            Cli.spec_items(globals))}, name),
          Laws.sub_key_of(Cli.find_sub(items, name)),
          Laws.p19_sub(items, Cli.spec_items(globals), p, name)) :
        ScopeFound(Laws.scope_at(tail, Laws.scan_enter(_,
            Cli.ScanState{Cli.Scope{p, Cli.spec_node(items,
              Cli.spec_items(globals))}, events, resting, count, external,
              issue})),
          Cli.scope_args(tail, Cli.sub_items(Cli.find_sub(items, name)),
            List.append(&2, Cli.Item, Cli.global_items(items), globals)), id)
      scope_step(Cli.find_sub(items, name), tail, items, globals, p, events,
        resting, count, external, issue, id,
        p2 => ev2 => kids => scope_walk(tail, kids,
          List.append(&2, Cli.Item, Cli.global_items(items), globals), p2,
          ev2, resting, 0n, external, issue, id))

# arg_verdict is verdict_ref, whatever it found.
def arg_verdict_same(found: Maybe<&2, Cli.ArgInfo>, -id: String,
    -name: String, -path: List<&2, String>, -want: Cli.Want) ->
    {Cli.arg_verdict(found, id, name, path, want)
      == Laws.verdict_ref(found, id, name, path, want) : Maybe<&2, String>}:
  match found:
    case None{}: {==}
    case Some{Cli.ArgInfo{key, usage, short, long, kind, attrs}}: {==}

def verdict_scope(scope: Maybe<&2, Cli.Scope>, -name: String,
    -about: String, -items: List<&2, Cli.Item>, -path: List<&2, String>,
    id: String, -want: Cli.Want,
    found: ScopeFound(scope, Cli.scope_args(path, items, []), id)) ->
    Laws.verdict_at(scope, name, about, items, path, id, want):
  match scope:
    case None{}: Unit{}
    case Some{s}:
      %found : {Cli.arg_verdict(_, id, name, path, want)
        == Laws.verdict_ref(Cli.find_spec_info(Cli.scope_arg_items(s), id,
          None{}), id, name, path, want) : Maybe<&2, String>}
      arg_verdict_same(Cli.find_spec_info(Cli.scope_arg_items(s), id, None{}),
        id, name, path, want)

def Laws.p19_verdict(name, about, items, path, id, want):
  verdict_scope(Laws.scope_at(path,
      Some{Cli.scan_start(Cli.Cmd{name, about, items})}), name, about, items,
    path, id, want, scope_walk(path, items, [], [], [], False{}, 0n, None{},
      None{}, id))

# P20: key_go reads a key one word at a time with word_rest, while
# command_words takes the words String.split cuts. cut reads the first
# word as String.split does (split_cut) and as word_rest does (word_cut).

# A text's first word, cut at its first space, and the text after that
# space, if any; String.split cuts at the same spaces.
type WordCut is Data:
  WordCut{word: String, rest: Maybe<&2, String>}

def cut_word(k: WordCut) -> String:
  match k:
    case WordCut{word, rest}: word

def cut_rest(k: WordCut) -> Maybe<&2, String>:
  match k:
    case WordCut{word, rest}: rest

def cut_push(c: Char, k: WordCut) -> WordCut:
  match k:
    case WordCut{word, rest}: WordCut{SCon{c, word}, rest}

def cut_pick(space: Bool, c: Char, t: String, k: WordCut) -> WordCut:
  match space:
    case True{}: WordCut{SNil{}, Some{t}}
    case False{}: cut_push(c, k)

def cut(text: String) -> WordCut:
  match text:
    case SNil{}: WordCut{SNil{}, None{}}
    case SCon{+c, +t}: cut_pick(Char.is_eq(c, ' '), c, t, cut(t))

def rest_words(rest: Maybe<&2, String>) -> List<&2, String>:
  match rest:
    case None{}: []
    case Some{t}: String.split(t, ' ')

def push_word(-c: Char, k: WordCut) ->
    {SCon{c, cut_word(k)} == cut_word(cut_push(c, k)) : String}:
  match k:
    case WordCut{word, rest}: {==}

def push_rest(-c: Char, k: WordCut) ->
    {cut_rest(k) == cut_rest(cut_push(c, k)) : Maybe<&2, String>}:
  match k:
    case WordCut{word, rest}: {==}

def cut_step(b: Bool, -c: Char, -t: String, k: WordCut,
    ih: {cut_word(k) <> rest_words(cut_rest(k)) == String.split(t, ' ')
      : List<&2, String>}) ->
    {cut_word(cut_pick(b, c, t, k)) <> rest_words(cut_rest(cut_pick(b, c, t, k)))
      == String.split.fin(c, String.split(t, ' '), b) : List<&2, String>}:
  match b:
    case True{}: {==}
    case False{}:
      match k:
        case WordCut{word, rest}:
          %ih : {SCon{c, word} <> rest_words(rest)
            == String.split.push(c, _) : List<&2, String>}
          {==}

def split_cut(text: String) ->
    {cut_word(cut(text)) <> rest_words(cut_rest(cut(text)))
      == String.split(text, ' ') : List<&2, String>}:
  match text:
    case SNil{}: {==}
    case SCon{+c, +t}: cut_step(Char.is_eq(c, ' '), c, t, cut(t), split_cut(t))

# What word_rest does with a name or text whose head c is not a space.
def SpOther(c: Char) -> Type:
  (@xs: String -> @y: Char -> @ys: String ->
    {Cli.word_rest(xs, ys, Char.is_eq(c, y))
      == Cli.word_rest(SCon{c, xs}, SCon{y, ys}, True{}) : Maybe<&2, Maybe<&2, String>>}) &
  ((@xs: String -> {None{} == Cli.word_rest(SCon{c, xs}, SNil{}, True{})
    : Maybe<&2, Maybe<&2, String>>}) &
  ((@t: String -> {None{} == Cli.word_rest(SNil{}, SCon{c, t}, True{})
    : Maybe<&2, Maybe<&2, String>>}) &
  ((@t: String -> {None{} == Cli.word_rest(SNil{}, SCon{c, t}, False{})
    : Maybe<&2, Maybe<&2, String>>}) &
  ((@xs: String -> {None{} == Cli.word_rest(SCon{c, xs}, SNil{}, False{})
    : Maybe<&2, Maybe<&2, String>>}) &
  (@xs: String -> @y: Char -> @ys: String ->
    {None{} == Cli.word_rest(SCon{c, xs}, SCon{y, ys}, False{})
      : Maybe<&2, Maybe<&2, String>>})))))

def SpView(c: Char) -> Type:
  {Chr{32} == c : Char} | SpOther(c)

# Arms: python3 tools/charsplit.py '(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))' 32
def sp_view(c: Char) -> SpView(c):
  match c:
    case Chr{U32{WCon{True{}, _}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{True{}, _}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inl{{==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{(xs => y => ys => {==}, (xs => {==}, (t => {==}, (t => {==}, (xs => {==}, xs => y => ys => {==})))))}

def false_same(a: String, b: String) ->
    {False{} == Cli.same_go(a, b, False{}) : Bool}:
  match a b:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{h, t}: {==}
    case SCon{h, t} SNil{}: {==}
    case SCon{x, xt} SCon{y, yt}: {==}

def opt_disc(m: Maybe<&2, Maybe<&2, String>>) -> Data:
  match m:
    case None{}: Empty
    case Some{x}: Unit

def space_absurd(-c: Char, r: {Chr{32} == c : Char},
    h: {Cli.word_rest(SNil{}, SCon{c, SNil{}}, True{}) == None{} : Maybe<&2, Maybe<&2, String>>}) ->
    Empty:
  %h : opt_disc(_)
  %r : opt_disc(Cli.word_rest(SNil{}, SCon{_, SNil{}}, True{}))
  Unit{}

# A char word_rest treats as no space is no space to Char.is_eq.
def not_space(b: Bool, +c: Char,
    a3: @t: String -> {None{} == Cli.word_rest(SNil{}, SCon{c, t}, True{})
      : Maybe<&2, Maybe<&2, String>>},
    e: {b == Char.is_eq(c, ' ') : Bool}) ->
    {False{} == Char.is_eq(c, ' ') : Bool}:
  match b:
    case False{}: e
    case True{}:
      Empty.absurd({False{} == Char.is_eq(c, ' ') : Bool},
        space_absurd(c, Equal.sym(Char, c, Chr{32},
          char_reflect(c, ' ', Equal.sym(Bool, True{}, Char.is_eq(c, ' '),
            e))),
          Equal.sym(Maybe<&2, Maybe<&2, String>>, None{},
            Cli.word_rest(SNil{}, SCon{c, SNil{}}, True{}), a3(SNil{}))))

def space_contra(-c: Char, r: {Chr{32} == c : Char},
    eb: {Char.is_eq(c, ' ') == False{} : Bool}) -> Empty:
  %eb : bool_disc(_)
  %r : bool_disc(Char.is_eq(_, ' '))
  Unit{}

def space_sym(b: Bool, +c: Char, eb: {Char.is_eq(c, ' ') == False{} : Bool},
    ed: {b == Char.is_eq(' ', c) : Bool}) ->
    {False{} == Char.is_eq(' ', c) : Bool}:
  match b:
    case False{}: ed
    case True{}:
      Empty.absurd({False{} == Char.is_eq(' ', c) : Bool},
        space_contra(c, char_reflect(' ', c,
          Equal.sym(Bool, True{}, Char.is_eq(' ', c), ed)), eb))

def wrf_nil(-c: Char, t: String, v: SpView(c)) ->
    {None{} == Cli.word_rest(SNil{}, SCon{c, t}, False{}) : Maybe<&2, Maybe<&2, String>>}:
  match v:
    case Inl{e}:
      %e : {None{} == Cli.word_rest(SNil{}, SCon{_, t}, False{}) : Maybe<&2, Maybe<&2, String>>}
      {==}
    case Inr{(a1, (a2, (a3, (a4, (a5, a6)))))}: a4(t)

def wrf_cons_nil(-x: Char, xs: String, v: SpView(x)) ->
    {None{} == Cli.word_rest(SCon{x, xs}, SNil{}, False{}) : Maybe<&2, Maybe<&2, String>>}:
  match v:
    case Inl{e}:
      %e : {None{} == Cli.word_rest(SCon{_, xs}, SNil{}, False{}) : Maybe<&2, Maybe<&2, String>>}
      {==}
    case Inr{(a1, (a2, (a3, (a4, (a5, a6)))))}: a5(xs)

def wrf_cons(-x: Char, xs: String, c: Char, t: String, v: SpView(x)) ->
    {None{} == Cli.word_rest(SCon{x, xs}, SCon{c, t}, False{}) : Maybe<&2, Maybe<&2, String>>}:
  match v:
    case Inl{e}:
      %e : {None{} == Cli.word_rest(SCon{_, xs}, SCon{c, t}, False{})
        : Maybe<&2, Maybe<&2, String>>}
      {==}
    case Inr{(a1, (a2, (a3, (a4, (a5, a6)))))}: a6(xs, c, t)

def word_rest_false(name: String, text: String) ->
    {None{} == Cli.word_rest(name, text, False{}) : Maybe<&2, Maybe<&2, String>>}:
  match name text:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{+c, t}: wrf_nil(c, t, sp_view(c))
    case SCon{+x, xs} SNil{}: wrf_cons_nil(x, xs, sp_view(x))
    case SCon{+x, xs} SCon{c, t}: wrf_cons(x, xs, c, t, sp_view(x))

def wr_nil_other(b: Bool, +c: Char, +t: String,
    a3: @t: String -> {None{} == Cli.word_rest(SNil{}, SCon{c, t}, True{})
      : Maybe<&2, Maybe<&2, String>>},
    e: {b == Char.is_eq(c, ' ') : Bool}) ->
    {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SNil{}, cut_word(cut_pick(b, c, t, cut(t)))),
      Some{cut_rest(cut_pick(b, c, t, cut(t)))}, None{})
      == Cli.word_rest(SNil{}, SCon{c, t}, True{}) : Maybe<&2, Maybe<&2, String>>}:
  match b:
    case False{}:
      %a3(t) : {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SNil{},
        cut_word(cut_push(c, cut(t)))), Some{cut_rest(cut_push(c, cut(t)))},
        None{}) == _ : Maybe<&2, Maybe<&2, String>>}
      %push_word(c, cut(t)) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SNil{}, _),
          Some{cut_rest(cut_push(c, cut(t)))}, None{}) == None{} : Maybe<&2, Maybe<&2, String>>}
      {==}
    case True{}:
      Empty.absurd({Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SNil{},
        cut_word(cut_pick(True{}, c, t, cut(t)))),
        Some{cut_rest(cut_pick(True{}, c, t, cut(t)))}, None{})
        == Cli.word_rest(SNil{}, SCon{c, t}, True{}) : Maybe<&2, Maybe<&2, String>>},
        space_absurd(c, Equal.sym(Char, c, Chr{32},
          char_reflect(c, ' ', Equal.sym(Bool, True{}, Char.is_eq(c, ' '),
            e))),
          Equal.sym(Maybe<&2, Maybe<&2, String>>, None{},
            Cli.word_rest(SNil{}, SCon{c, SNil{}}, True{}), a3(SNil{}))))

def wr_nil_cons(+c: Char, +t: String, v: SpView(c)) ->
    {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SNil{}, cut_word(cut(SCon{c, t}))),
      Some{cut_rest(cut(SCon{c, t}))}, None{})
      == Cli.word_rest(SNil{}, SCon{c, t}, True{}) : Maybe<&2, Maybe<&2, String>>}:
  match v:
    case Inl{e}:
      %e : {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SNil{}, cut_word(cut(SCon{_, t}))),
        Some{cut_rest(cut(SCon{_, t}))}, None{})
        == Cli.word_rest(SNil{}, SCon{_, t}, True{}) : Maybe<&2, Maybe<&2, String>>}
      {==}
    case Inr{(a1, (a2, (a3, (a4, (a5, a6)))))}:
      wr_nil_other(Char.is_eq(c, ' '), c, t, a3, {==})

def wr_cons_nil(-x: Char, xs: String, v: SpView(x)) ->
    {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SCon{x, xs}, cut_word(cut(SNil{}))),
      Some{cut_rest(cut(SNil{}))}, None{})
      == Cli.word_rest(SCon{x, xs}, SNil{}, True{}) : Maybe<&2, Maybe<&2, String>>}:
  match v:
    case Inl{e}:
      %e : {None{} == Cli.word_rest(SCon{_, xs}, SNil{}, True{}) : Maybe<&2, Maybe<&2, String>>}
      {==}
    case Inr{(a1, (a2, (a3, (a4, (a5, a6)))))}: a2(xs)

def space_head(b: Bool, xs: String, +c: Char, +t: String,
    eb: {b == Char.is_eq(c, ' ') : Bool}) ->
    {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SCon{Chr{32}, xs},
      cut_word(cut_pick(b, c, t, cut(t)))),
      Some{cut_rest(cut_pick(b, c, t, cut(t)))}, None{}) == None{} : Maybe<&2, Maybe<&2, String>>}:
  match b:
    case True{}: {==}
    case False{}:
      %push_word(c, cut(t)) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SCon{Chr{32}, xs}, _),
          Some{cut_rest(cut_push(c, cut(t)))}, None{}) == None{} : Maybe<&2, Maybe<&2, String>>}
      %space_sym(Char.is_eq(' ', c), c,
        Equal.sym(Bool, False{}, Char.is_eq(c, ' '), eb), {==}) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_go(xs, cut_word(cut(t)), _),
          Some{cut_rest(cut_push(c, cut(t)))}, None{}) == None{} : Maybe<&2, Maybe<&2, String>>}
      %false_same(xs, cut_word(cut(t))) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, _, Some{cut_rest(cut_push(c, cut(t)))}, None{})
          == None{} : Maybe<&2, Maybe<&2, String>>}
      {==}

def wr_step(d: Bool, +xs: String, +t: String,
    ih: {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(xs, cut_word(cut(t))),
      Some{cut_rest(cut(t))}, None{}) == Cli.word_rest(xs, t, True{})
      : Maybe<&2, Maybe<&2, String>>}) ->
    {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_go(xs, cut_word(cut(t)), d),
      Some{cut_rest(cut(t))}, None{}) == Cli.word_rest(xs, t, d) : Maybe<&2, Maybe<&2, String>>}:
  match d:
    case True{}: ih
    case False{}:
      %word_rest_false(xs, t) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_go(xs, cut_word(cut(t)), False{}),
          Some{cut_rest(cut(t))}, None{}) == _ : Maybe<&2, Maybe<&2, String>>}
      %false_same(xs, cut_word(cut(t))) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, _, Some{cut_rest(cut(t))}, None{}) == None{} : Maybe<&2, Maybe<&2, String>>}
      {==}

def wr_other(b: Bool, +x: Char, +xs: String, +c: Char, +t: String,
    a3: @t: String -> {None{} == Cli.word_rest(SNil{}, SCon{x, t}, True{})
      : Maybe<&2, Maybe<&2, String>>},
    ih: {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(xs, cut_word(cut(t))),
      Some{cut_rest(cut(t))}, None{}) == Cli.word_rest(xs, t, True{})
      : Maybe<&2, Maybe<&2, String>>},
    eb: {b == Char.is_eq(c, ' ') : Bool}) ->
    {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SCon{x, xs},
      cut_word(cut_pick(b, c, t, cut(t)))),
      Some{cut_rest(cut_pick(b, c, t, cut(t)))}, None{})
      == Cli.word_rest(xs, t, Char.is_eq(x, c)) : Maybe<&2, Maybe<&2, String>>}:
  match b:
    case True{}:
      %Equal.sym(Char, c, Chr{32}, char_reflect(c, ' ',
        Equal.sym(Bool, True{}, Char.is_eq(c, ' '), eb))) :
        {None{} == Cli.word_rest(xs, t, Char.is_eq(x, _)) : Maybe<&2, Maybe<&2, String>>}
      %not_space(Char.is_eq(x, ' '), x, a3, {==}) :
        {None{} == Cli.word_rest(xs, t, _) : Maybe<&2, Maybe<&2, String>>}
      word_rest_false(xs, t)
    case False{}:
      %push_word(c, cut(t)) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SCon{x, xs}, _),
          Some{cut_rest(cut_push(c, cut(t)))}, None{})
          == Cli.word_rest(xs, t, Char.is_eq(x, c)) : Maybe<&2, Maybe<&2, String>>}
      %push_rest(c, cut(t)) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_go(xs, cut_word(cut(t)), Char.is_eq(x, c)),
          Some{_}, None{}) == Cli.word_rest(xs, t, Char.is_eq(x, c)) : Maybe<&2, Maybe<&2, String>>}
      wr_step(Char.is_eq(x, c), xs, t, ih)

def wr_cons(+x: Char, +xs: String, +c: Char, +t: String,
    ih: {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(xs, cut_word(cut(t))),
      Some{cut_rest(cut(t))}, None{}) == Cli.word_rest(xs, t, True{})
      : Maybe<&2, Maybe<&2, String>>},
    v: SpView(x)) ->
    {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SCon{x, xs}, cut_word(cut(SCon{c, t}))),
      Some{cut_rest(cut(SCon{c, t}))}, None{})
      == Cli.word_rest(SCon{x, xs}, SCon{c, t}, True{}) : Maybe<&2, Maybe<&2, String>>}:
  match v:
    case Inl{e}:
      %e : {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SCon{_, xs},
        cut_word(cut(SCon{c, t}))), Some{cut_rest(cut(SCon{c, t}))}, None{})
        == Cli.word_rest(SCon{_, xs}, SCon{c, t}, True{}) : Maybe<&2, Maybe<&2, String>>}
      space_head(Char.is_eq(c, ' '), xs, c, t, {==})
    case Inr{(a1, (a2, (a3, (a4, (a5, a6)))))}:
      %a1(xs, c, t) :
        {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(SCon{x, xs}, cut_word(cut(SCon{c, t}))),
          Some{cut_rest(cut(SCon{c, t}))}, None{}) == _ : Maybe<&2, Maybe<&2, String>>}
      wr_other(Char.is_eq(c, ' '), x, xs, c, t, a3, ih, {==})

def word_cut(name: String, text: String) ->
    {Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(name, cut_word(cut(text))),
      Some{cut_rest(cut(text))}, None{})
      == Cli.word_rest(name, text, True{}) : Maybe<&2, Maybe<&2, String>>}:
  match name text:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{+c, +t}: wr_nil_cons(c, t, sp_view(c))
    case SCon{+x, +xs} SNil{}: wr_cons_nil(x, xs, sp_view(x))
    case SCon{+x, +xs} SCon{+c, +t}:
      wr_cons(x, xs, c, t, word_cut(xs, t), sp_view(x))

def cw_none(ws: List<&2, String>) ->
    {False{} == Laws.command_words(ws, None{}) : Bool}:
  match ws:
    case Nil{}: {==}
    case w <> t: {==}

# The tail's walk, with its words cut at the first space.
def split_tail(+text: String, -tail: List<&2, Cli.Item>,
    ih: {Cli.key_go(tail, text, Cli.key_step(tail, text))
      == Laws.command_words(String.split(text, ' '), Some{tail}) : Bool}) ->
    {Cli.key_go(tail, text, Cli.key_step(tail, text))
      == Laws.command_words(rest_words(cut_rest(cut(text))),
        Laws.user_found(Laws.named_sub(tail, cut_word(cut(text))))) : Bool}:
  %Equal.sym(List<&2, String>,
    cut_word(cut(text)) <> rest_words(cut_rest(cut(text))),
    String.split(text, ' '), split_cut(text)) :
    {Cli.key_go(tail, text, Cli.key_step(tail, text))
      == Laws.command_words(_, Some{tail}) : Bool}
  ih

def builtin_step(builtin: Bool, rest: Maybe<&2, String>, -name: String,
    -about: String, -children: List<&2, Cli.Item>,
    -tail: List<&2, Cli.Item>, -text: String,
    ih: @r: String -> {Cli.key_go(children, r, Cli.key_step(children, r))
      == Laws.command_words(String.split(r, ' '), Some{children}) : Bool}) ->
    {Cli.key_go(Cli.Sub{name, about, children} <> tail, text,
      Cli.key_user(builtin, rest))
      == Laws.command_words(rest_words(rest),
        Bool.pick(Maybe<&2, List<&2, Cli.Item>>, builtin, None{}, Some{children})) : Bool}:
  match builtin rest:
    case True{} None{}: {==}
    case True{} Some{r}: cw_none(String.split(r, ' '))
    case False{} None{}: {==}
    case False{} Some{r}: ih(r)

def sub_step(same: Bool, -name: String, -about: String,
    children: List<&2, Cli.Item>, -tail: List<&2, Cli.Item>, +text: String,
    ih_tail: {Cli.key_go(tail, text, Cli.key_step(tail, text))
      == Laws.command_words(String.split(text, ' '), Some{tail}) : Bool},
    ih: @r: String -> {Cli.key_go(children, r, Cli.key_step(children, r))
      == Laws.command_words(String.split(r, ' '), Some{children}) : Bool}) ->
    {Cli.key_go(Cli.Sub{name, about, children} <> tail, text,
      Cli.key_word(Bool.pick(Maybe<&2, Maybe<&2, String>>, same, Some{cut_rest(cut(text))}, None{}),
        children))
      == Laws.command_words(rest_words(cut_rest(cut(text))),
        Laws.user_found(Bool.pick(Maybe<&2, List<&2, Cli.Item>>, same, Some{children},
          Laws.named_sub(tail, cut_word(cut(text)))))) : Bool}:
  match same:
    case False{}: split_tail(text, tail, ih_tail)
    case True{}:
      builtin_step(Cli.has_builtin(children), cut_rest(cut(text)), name,
        about, children, tail, text, ih)

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Sub cli.bend Item '$P <> +tail' '%split_cut(text) :\n  {Cli.key_go(tail, text, Cli.key_step(tail, text))\n    == Laws.command_words(_, Some{$H <> tail}) : Bool}\nsplit_tail(text, tail, route_go(tail, text))'
def route_go(items: List<&2, Cli.Item>, +text: String) ->
    {Cli.key_go(items, text, Cli.key_step(items, text))
      == Laws.command_words(String.split(text, ' '), Some{items}) : Bool}:
  match items:
    case Nil{}:
      %split_cut(text) : {False{} == Laws.command_words(_, Some{Nil{}}) : Bool}
      cw_none(rest_words(cut_rest(cut(text))))
    case Cli.Sub{+name, about, +children} <> +tail:
      %split_cut(text) :
        {Cli.key_go(Cli.Sub{name, about, children} <> tail, text,
          Cli.key_word(Cli.word_rest(name, text, True{}), children))
          == Laws.command_words(_, Some{Cli.Sub{name, about, children} <> tail})
          : Bool}
      %word_cut(name, text) :
        {Cli.key_go(Cli.Sub{name, about, children} <> tail, text,
          Cli.key_word(_, children))
          == Laws.command_words(rest_words(cut_rest(cut(text))),
            Laws.user_found(Bool.pick(Maybe<&2, List<&2, Cli.Item>>,
              String.eq(name, cut_word(cut(text))), Some{children},
              Laws.named_sub(tail, cut_word(cut(text)))))) : Bool}
      %Laws.p18_text(name, cut_word(cut(text))) :
        {Cli.key_go(Cli.Sub{name, about, children} <> tail, text,
          Cli.key_word(Bool.pick(Maybe<&2, Maybe<&2, String>>, Cli.same_text(name, cut_word(cut(text))),
            Some{cut_rest(cut(text))}, None{}), children))
          == Laws.command_words(rest_words(cut_rest(cut(text))),
            Laws.user_found(Bool.pick(Maybe<&2, List<&2, Cli.Item>>, _, Some{children},
              Laws.named_sub(tail, cut_word(cut(text)))))) : Bool}
      sub_step(Cli.same_text(name, cut_word(cut(text))), name, about,
        children, tail, text, route_go(tail, text),
        r => route_go(children, r))
    case Cli.Arg{x0, x1, x2} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Arg{x0, x1, x2} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Version{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Version{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Alias{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Alias{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Hidden{} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Hidden{} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Example{x0, x1} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Example{x0, x1} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.After{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.After{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.SubOptional{} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.SubOptional{} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.External{} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.External{} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Exclusive{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Exclusive{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.NeedOne{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.NeedOne{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Id{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Id{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Required{} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Required{} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.AttrDefault{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.AttrDefault{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.AttrEnv{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.AttrEnv{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Global{} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Global{} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Heading{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Heading{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.As{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.As{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.OneOf{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.OneOf{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Delim{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Delim{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Hyphen{} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Hyphen{} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Rest{} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Rest{} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Bare{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Bare{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Conflicts{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Conflicts{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Requires{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Requires{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Group{x0} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Group{x0} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))
    case Cli.Builtin{} <> +tail:
      %split_cut(text) :
        {Cli.key_go(tail, text, Cli.key_step(tail, text))
          == Laws.command_words(_, Some{Cli.Builtin{} <> tail}) : Bool}
      split_tail(text, tail, route_go(tail, text))

def Laws.p20(key, items):
  match key:
    case SNil{}: {==}
    case SCon{h, t}: route_go(items, SCon{h, t})

# P20 route. The table holds callbacks, so no proof can walk it twice. And
# code specific to Call(A) wraps each callback it names as m => c(m), which
# the kernel (no eta) tells apart from c inside data. So tab_cons walks the
# table once in generic code, and route_tab instantiates it, naming a
# callback only where route_answer applies it.

# A hit found before keys and values stays found.
def Stays(a, -A: Kind(a), keys: List<&2, String>, values: List<a, A>,
    key: String) -> Type:
  @-h: A ->
    {Cli.find_by_key_go(a, A, keys, values, key, Some{h}) == Some{h}
      : Maybe<a, A>}

# table's keys and values as unzip_keyed splits them; find_by_key and keyed
# agree there; non_command finds B's key; and keyed's answer through F is L's.
def Tab(a, -A: Kind(a), -D: Type, -F: Maybe<a, A> -> D,
    -L: List<(String & A)> -> D, -B: List<(String & A)> -> Maybe<&2, String>,
    table: List<(String & A)>, key: String, items: List<&2, Cli.Item>)
    -> Type:
  &keys: List<&2, String> -> &values: List<a, A> ->
  ({(keys, values) == Cli.unzip_keyed(a, A, table)
      : (List<&2, String> & List<a, A>)} &
   ({Cli.find_by_key(a, A, keys, values, key)
       == Laws.keyed(a, A, keys, values, key) : Maybe<a, A>} &
    (Stays(a, A, keys, values, key) &
     ({Cli.non_command(keys, items) == B(table) : Maybe<&2, String>} &
      {F(Laws.keyed(a, A, keys, values, key)) == L(table) : D}))))

def tab_unzip(a, -A: Kind(a), -k: String, -v: A,
    -tail: List<(String & A)>, -keys: List<&2, String>,
    -values: List<a, A>,
    e: {(keys, values) == Cli.unzip_keyed(a, A, tail)
      : (List<&2, String> & List<a, A>)}) ->
    {(k <> keys, v <> values) == Cli.unzip_keyed(a, A, (k, v) <> tail)
      : (List<&2, String> & List<a, A>)}:
  %e : {(k <> keys, v <> values) == Cli.keyed_cons(a, A, k, v, _)
    : (List<&2, String> & List<a, A>)}
  {==}

# by_key_hit's answer, then the walk on from None.
def hit_pick(a, -A: Kind(a), hit: Bool, -v: A, -keys: List<&2, String>,
    -values: List<a, A>, -key: String, stays: Stays(a, A, keys, values, key))
    -> {Cli.find_by_key_go(a, A, keys, values, key,
        Cli.by_key_hit(a, A, hit, v))
      == Bool.pick(Maybe<a, A>, hit, Some{v},
        Cli.find_by_key_go(a, A, keys, values, key, None{}))
      : Maybe<a, A>}:
  match hit:
    case True{}: stays(v)
    case False{}: {==}

def tab_find(a, -A: Kind(a), +k: String, -v: A, -keys: List<&2, String>,
    -values: List<a, A>, +key: String,
    e: {Cli.find_by_key(a, A, keys, values, key)
      == Laws.keyed(a, A, keys, values, key) : Maybe<a, A>},
    stays: Stays(a, A, keys, values, key)) ->
    {Cli.find_by_key(a, A, k <> keys, v <> values, key)
      == Laws.keyed(a, A, k <> keys, v <> values, key) : Maybe<a, A>}:
  %e : {Cli.find_by_key(a, A, k <> keys, v <> values, key)
    == Bool.pick(Maybe<a, A>, String.eq(k, key), Some{v}, _) : Maybe<a, A>}
  %Laws.p18_text(k, key) : {Cli.find_by_key(a, A, k <> keys, v <> values, key)
    == Bool.pick(Maybe<a, A>, _, Some{v},
      Cli.find_by_key(a, A, keys, values, key)) : Maybe<a, A>}
  hit_pick(a, A, Cli.same_text(k, key), v, keys, values, key, stays)

def tab_bad(a, -A: Kind(a), -B: List<(String & A)> -> Maybe<&2, String>,
    +k: String, -v: A, -tail: List<(String & A)>, -keys: List<&2, String>,
    +items: List<&2, Cli.Item>,
    e: {Cli.non_command(keys, items) == B(tail) : Maybe<&2, String>},
    step: {Bool.pick(Maybe<&2, String>,
        Laws.command_words(Laws.key_words(k), Some{items}), B(tail), Some{k})
      == B((k, v) <> tail) : Maybe<&2, String>}) ->
    {Cli.non_command(k <> keys, items) == B((k, v) <> tail)
      : Maybe<&2, String>}:
  %step : {Cli.non_command(k <> keys, items) == _ : Maybe<&2, String>}
  %e : {Cli.non_command(k <> keys, items)
    == Bool.pick(Maybe<&2, String>,
      Laws.command_words(Laws.key_words(k), Some{items}), _, Some{k})
    : Maybe<&2, String>}
  %Laws.p20(k, items) : {Cli.non_command(k <> keys, items)
    == Bool.pick(Maybe<&2, String>, _, Cli.non_command(keys, items),
      Some{k}) : Maybe<&2, String>}
  {==}

# keyed's answer through F at the entry (k, v): hit says it is L's when k is
# key, and miss that L skips the entry otherwise.
def tab_pick(a, -A: Kind(a), -D: Type, -F: Maybe<a, A> -> D,
    -L: List<(String & A)> -> D, hit: Bool, -k: String, -v: A,
    -tail: List<(String & A)>, -keys: List<&2, String>, -values: List<a, A>,
    -key: String, same: {hit == String.eq(k, key) : Bool},
    rest: {F(Laws.keyed(a, A, keys, values, key)) == L(tail) : D},
    on_hit: {True{} == String.eq(k, key) : Bool} ->
      {F(Some{v}) == L((k, v) <> tail) : D},
    on_miss: {False{} == String.eq(k, key) : Bool} ->
      {L(tail) == L((k, v) <> tail) : D}) ->
    {F(Bool.pick(Maybe<a, A>, hit, Some{v},
        Laws.keyed(a, A, keys, values, key))) == L((k, v) <> tail) : D}:
  match hit:
    case True{}: on_hit(same)
    case False{}:
      %on_miss(same) : {F(Laws.keyed(a, A, keys, values, key)) == _ : D}
      rest

def tab_cons(a, -A: Kind(a), -D: Type, -F: Maybe<a, A> -> D,
    -L: List<(String & A)> -> D, -B: List<(String & A)> -> Maybe<&2, String>,
    entry: (String & A), -tail: List<(String & A)>, +key: String,
    +items: List<&2, Cli.Item>, ih: Tab(a, A, D, F, L, B, tail, key, items),
    on_hit: @-k: String -> @-v: A -> {True{} == String.eq(k, key) : Bool} ->
      {F(Some{v}) == L((k, v) <> tail) : D},
    on_miss: @-k: String -> @-v: A -> {False{} == String.eq(k, key) : Bool} ->
      {L(tail) == L((k, v) <> tail) : D},
    on_bad: @-k: String -> @-v: A ->
      {Bool.pick(Maybe<&2, String>,
          Laws.command_words(Laws.key_words(k), Some{items}), B(tail),
          Some{k})
        == B((k, v) <> tail) : Maybe<&2, String>}) ->
    Tab(a, A, D, F, L, B, entry <> tail, key, items):
  match entry:
    case (+k, v):
      match ih:
        case (+keys, (values, (e1, (e2, (stays, (e3, e4)))))):
          (k <> keys, (v <> values,
            (tab_unzip(a, A, k, v, tail, keys, values, e1),
            (tab_find(a, A, k, v, keys, values, key, e2, stays),
            (h => {==},
            (tab_bad(a, A, B, k, v, tail, keys, items, e3, on_bad(k, v)),
            tab_pick(a, A, D, F, L, String.eq(k, key), k, v, tail, keys,
              values, key, {==}, e4, on_hit(k, v), on_miss(k, v))))))))

# route_tab's F, L and B: route_answer at found, at table_call's answer, and
# table_bad's.
def route_tab(-A: Type, table: List<(String & Cli.Call(A))>, +key: String,
    +items: List<&2, Cli.Item>, -bad: Maybe<&2, String>, -text: String,
    -m: Cli.Matches) ->
    Tab(&1, Cli.Call(A), Cli.Dec(A),
      f => Laws.route_answer(A, f, bad, text, m),
      t => Laws.route_answer(A, Laws.table_call(A, t, key), bad, text, m),
      t => Laws.table_bad(A, t, items), table, key, items):
  match table:
    case Nil{}: ([], ([], ({==}, ({==}, (h => {==}, ({==}, {==}))))))
    case entry <> tail:
      tab_cons(&1, Cli.Call(A), Cli.Dec(A),
        f => Laws.route_answer(A, f, bad, text, m),
        t => Laws.route_answer(A, Laws.table_call(A, t, key), bad, text, m),
        t => Laws.table_bad(A, t, items), entry, tail, key, items,
        route_tab(A, tail, key, items, bad, text, m),
        k => v => e =>
          (%e : {Laws.route_answer(A, Some{v}, bad, text, m)
              == Laws.route_answer(A,
                Bool.pick(Maybe<Cli.Call(A)>, _, Some{v},
                  Laws.table_call(A, tail, key)), bad, text, m)
              : Cli.Dec(A)}
            {==}),
        k => v => e =>
          (%e : {Laws.route_answer(A, Laws.table_call(A, tail, key), bad,
                text, m)
              == Laws.route_answer(A,
                Bool.pick(Maybe<Cli.Call(A)>, _, Some{v},
                  Laws.table_call(A, tail, key)), bad, text, m)
              : Cli.Dec(A)}
            {==}),
        k => v => {==})

# route_call is bad_answer, and route_found is route_answer, for any bad
# and found.
def bad_same(-A: Type, bad: Maybe<&2, String>, -call: Cli.Call(A),
    -m: Cli.Matches) ->
    {Cli.route_call(A, bad, call, m) == Laws.bad_answer(A, bad, call, m)
      : Cli.Dec(A)}:
  match bad:
    case None{}: {==}
    case Some{key}: {==}

def found_same(-A: Type, found: Maybe<Cli.Call(A)>, keys: List<&2, String>,
    -name: String, -about: String, items: List<&2, Cli.Item>,
    -path: List<&2, String>, -m: Cli.Matches) ->
    {Cli.route_found(A, found, keys, Cli.Cmd{name, about, items}, path, m)
      == Laws.route_answer(A, found, Cli.non_command(keys, items),
        String.join(name <> path, " "), m) : Cli.Dec(A)}:
  match found:
    case None{}: {==}
    case Some{call}: bad_same(A, Cli.non_command(keys, items), call, m)

def route_at(-A: Type, -name: String, -about: String,
    +items: List<&2, Cli.Item>, +path: List<&2, String>,
    -fields: List<&2, Cli.Field>, -external: Maybe<&2, Cli.ExternalArgs>,
    -table: List<(String & Cli.Call(A))>,
    tab: Tab(&1, Cli.Call(A), Cli.Dec(A),
      f => Laws.route_answer(A, f, Laws.table_bad(A, table, items),
        String.join(name <> path, " "),
        Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external}),
      t => Laws.route_answer(A, Laws.table_call(A, t, String.join(path, " ")),
        Laws.table_bad(A, table, items), String.join(name <> path, " "),
        Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external}),
      t => Laws.table_bad(A, t, items), table, String.join(path, " "),
      items)) ->
    {Cli.route_pick(A, Cli.unzip_keyed(&1, Cli.Call(A), table),
        Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
      == Laws.route_answer(A,
        Laws.table_call(A, table, String.join(path, " ")),
        Laws.table_bad(A, table, items), String.join(name <> path, " "),
        Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
      : Cli.Dec(A)}:
  match tab:
    case (+keys, (values, (e1, (e2, (stays, (e3, e4)))))):
      %e4 : {Cli.route_pick(A, Cli.unzip_keyed(&1, Cli.Call(A), table),
          Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
        == _ : Cli.Dec(A)}
      %e3 : {Cli.route_pick(A, Cli.unzip_keyed(&1, Cli.Call(A), table),
          Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
        == Laws.route_answer(A,
          Laws.keyed(&1, Cli.Call(A), keys, values, String.join(path, " ")),
          _, String.join(name <> path, " "),
          Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
        : Cli.Dec(A)}
      %e2 : {Cli.route_pick(A, Cli.unzip_keyed(&1, Cli.Call(A), table),
          Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
        == Laws.route_answer(A, _, Cli.non_command(keys, items),
          String.join(name <> path, " "),
          Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
        : Cli.Dec(A)}
      %e1 : {Cli.route_pick(A, _,
          Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
        == Laws.route_answer(A,
          Cli.find_by_key(&1, Cli.Call(A), keys, values,
            String.join(path, " ")), Cli.non_command(keys, items),
          String.join(name <> path, " "),
          Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})
        : Cli.Dec(A)}
      found_same(A, Cli.find_by_key(&1, Cli.Call(A), keys, values,
        String.join(path, " ")), keys, name, about, items, path,
        Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external})

def Laws.p20_route(A, name, about, items, path, fields, external, table):
  route_at(A, name, about, items, path, fields, external, table,
    route_tab(A, table, String.join(path, " "), items,
      Laws.table_bad(A, table, items), String.join(name <> path, " "),
      Cli.Matches{Cli.Cmd{name, about, items}, path, fields, external}))

# P21 sample: sample_align lines the field field_find picks up with the arg
# find_arg_info picks. lint_clean, deep_scope and find_clean carry what lint
# checks from problems(c) == [] down to that arg: a default its kind allows
# and value_issue accepts (DefaultOk), a delim only on a list (DelimOk), and
# one_of values its type accepts (ChoicesOk). core then reads its sample
# values under each want whose verdict passes. A proof that items are clean
# is a pair, which no def may use twice, so dup_deep hands a continuation two.

# The values the sample gives an arg: its default as resolve_default
# converts it, else a sample value.
def default_vals(found: Maybe<&2, String>, kind: Cli.UsageKind,
    attrs: List<&2, Cli.Item>) -> List<&2, String>:
  match found:
    case None{}: [Cli.sample_value(kind, attrs)]
    case Some{value}: Cli.env_values(kind, attrs, value)

def default_src(found: Maybe<&2, String>) -> Cli.Src:
  match found:
    case None{}: Cli.Argv{}
    case Some{value}: Cli.Default{}

def info_vals(info: Cli.ArgInfo) -> List<&2, String>:
  match info:
    case Cli.ArgInfo{id, usage, short, long, kind, +attrs}:
      default_vals(Cli.find_default(attrs), kind, attrs)

def info_src(info: Cli.ArgInfo) -> Cli.Src:
  match info:
    case Cli.ArgInfo{id, usage, short, long, kind, attrs}:
      default_src(Cli.find_default(attrs))

def found_vals(found: Maybe<&2, Cli.ArgInfo>) -> List<&2, String>:
  match found:
    case None{}: Nil{}
    case Some{info}: info_vals(info)

def sample_one_found(found: Maybe<&2, String>, id: String, usage: String,
    short: String, long: String, kind: Cli.UsageKind,
    attrs: List<&2, Cli.Item>) ->
    {[Cli.Field{id, default_vals(found, kind, attrs), default_src(found)}]
      == Cli.sample_field(Cli.resolve_default(found,
        Cli.ArgInfo{id, usage, short, long, kind, attrs}),
        Cli.ArgInfo{id, usage, short, long, kind, attrs})
      : List<&2, Cli.Field>}:
  match found:
    case None{}: {==}
    case Some{value}: {==}

def sample_one(info: Cli.ArgInfo) ->
    {[Cli.Field{Cli.info_id(info), info_vals(info), info_src(info)}]
      == Cli.sample_field(Cli.resolve_default(Cli.info_default(info), info),
        info) : List<&2, Cli.Field>}:
  match info:
    case Cli.ArgInfo{+id, +usage, +short, +long, +kind, +attrs}:
      sample_one_found(Cli.find_default(attrs), id, usage, short, long, kind,
        attrs)

def arg_go_some(items: List<&2, Cli.Item>, +id: String, -h: Cli.ArgInfo) ->
    {Some{h} == Cli.find_arg_go(items, id, Some{h})
      : Maybe<&2, Cli.ArgInfo>}:
  match items:
    case Nil{}: {==}
    case item <> tail: {==}

def field_seek_some(fields: List<&2, Cli.Field>, +id: String,
    -f: Cli.Field) -> {f == Cli.field_seek(fields, id, Some{f}) : Cli.Field}:
  match fields:
    case Nil{}: {==}
    case g <> tail: {==}

def vals_pick(hit: Bool, +info: Cli.ArgInfo, -key: String, -src: Cli.Src,
    +items: List<&2, Cli.Item>, +fields: List<&2, Cli.Field>, +id: String,
    ih: {found_vals(Cli.find_arg_go(items, id, None{}))
      == Cli.field_values(Cli.field_seek(fields, id, None{}))
      : List<&2, String>}) ->
    {found_vals(Cli.find_arg_go(items, id,
      Bool.pick(Maybe<&2, Cli.ArgInfo>, hit, Some{info}, None{})))
      == Cli.field_values(Cli.field_seek(fields, id,
        Bool.pick(Maybe<&2, Cli.Field>, hit,
          Some{Cli.Field{key, info_vals(info), src}}, None{})))
      : List<&2, String>}:
  match hit:
    case True{}:
      %arg_go_some(items, id, info) :
        {found_vals(_) == Cli.field_values(Cli.field_seek(fields, id,
          Some{Cli.Field{key, info_vals(info), src}})) : List<&2, String>}
      %field_seek_some(fields, id, Cli.Field{key, info_vals(info), src}) :
        {info_vals(info) == Cli.field_values(_) : List<&2, String>}
      {==}
    case False{}: ih

def aln(items: List<&2, Cli.Item>, +id: String) ->
    {found_vals(Cli.find_arg_go(items, id, None{}))
      == Cli.field_values(Cli.field_seek(Cli.sample_args(items), id, None{}))
      : List<&2, String>}:
  match items:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      %sample_one(Cli.arg_info(usage, attrs)) :
        {found_vals(Cli.find_arg_go(Cli.Arg{usage, help, attrs} <> tail, id,
          None{})) == Cli.field_values(Cli.field_seek(List.append(&2,
            Cli.Field, _, Cli.sample_args(tail)), id, None{}))
          : List<&2, String>}
      vals_pick(Cli.same_text(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), Cli.info_id(Cli.arg_info(usage, attrs)),
        info_src(Cli.arg_info(usage, attrs)), tail, Cli.sample_args(tail),
        id, aln(tail, id))
    case Cli.Sub{x0, x1, x2} <> tail: aln(tail, id)
    case Cli.Version{x0} <> tail: aln(tail, id)
    case Cli.Alias{x0} <> tail: aln(tail, id)
    case Cli.Hidden{} <> tail: aln(tail, id)
    case Cli.Example{x0, x1} <> tail: aln(tail, id)
    case Cli.After{x0} <> tail: aln(tail, id)
    case Cli.SubOptional{} <> tail: aln(tail, id)
    case Cli.External{} <> tail: aln(tail, id)
    case Cli.Exclusive{x0} <> tail: aln(tail, id)
    case Cli.NeedOne{x0} <> tail: aln(tail, id)
    case Cli.Id{x0} <> tail: aln(tail, id)
    case Cli.Required{} <> tail: aln(tail, id)
    case Cli.AttrDefault{x0} <> tail: aln(tail, id)
    case Cli.AttrEnv{x0} <> tail: aln(tail, id)
    case Cli.Global{} <> tail: aln(tail, id)
    case Cli.Heading{x0} <> tail: aln(tail, id)
    case Cli.As{x0} <> tail: aln(tail, id)
    case Cli.OneOf{x0} <> tail: aln(tail, id)
    case Cli.Delim{x0} <> tail: aln(tail, id)
    case Cli.Hyphen{} <> tail: aln(tail, id)
    case Cli.Rest{} <> tail: aln(tail, id)
    case Cli.Bare{x0} <> tail: aln(tail, id)
    case Cli.Conflicts{x0} <> tail: aln(tail, id)
    case Cli.Requires{x0} <> tail: aln(tail, id)
    case Cli.Group{x0} <> tail: aln(tail, id)
    case Cli.Builtin{} <> tail: aln(tail, id)

# The sample field field_find picks holds the values the sample gives the
# arg find_arg_info picks, or none when there is no such arg.
def sample_align(items: List<&2, Cli.Item>, +id: String) ->
    {found_vals(Cli.find_arg_info(items, id))
      == Cli.field_values(Cli.field_find(Cli.sample_args(items), id))
      : List<&2, String>}:
  aln(items, id)

# P21 sample leaves: what the values of an arg with those facts satisfy.

def DefaultOk(found: Maybe<&2, String>, +kind: Cli.UsageKind,
    attrs: List<&2, Cli.Item>) -> Type:
  match found:
    case None{}: Unit
    case Some{value}:
      {Cli.kind_default_allowed(kind) == True{} : Bool} &
        {Cli.value_issue(kind, attrs, value) == None{} : Maybe<&2, Cli.Bad>}

def DelimOk(found: Maybe<&2, Char>, kind: Cli.UsageKind) -> Type:
  match found:
    case None{}: Unit
    case Some{sep}: {Cli.kind_delim_allowed(kind) == True{} : Bool}

def ChoicesOk(found: Maybe<&2, List<&2, String>>,
    kind: Maybe<&2, Cli.ValueType>) -> Type:
  match found:
    case None{}: Unit
    case Some{values}:
      {Cli.choice_bad(values, kind, None{}) == None{} : Maybe<&2, Cli.Bad>}

def and_left(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) ->
    {a == True{} : Bool}:
  match a:
    case True{}: {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true_absurd(e))

def and_right(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) ->
    {b == True{} : Bool}:
  match a:
    case True{}: e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true_absurd(e))

def bad_none_disc(m: Maybe<&2, Cli.Bad>) -> Data:
  match m:
    case None{}: Empty
    case Some{b}: Unit

def bad_some_absurd(-b: Cli.Bad,
    e: {Some{b} == None{} : Maybe<&2, Cli.Bad>}) -> Empty:
  %e : bad_none_disc(_)
  Unit{}

def why_none_disc(m: Maybe<&2, String>) -> Data:
  match m:
    case None{}: Empty
    case Some{w}: Unit

def why_some_absurd(-w: String,
    e: {Some{w} == None{} : Maybe<&2, String>}) -> Empty:
  %e : why_none_disc(_)
  Unit{}

def bad_value_none(r: Maybe<&2, String>, -value: String,
    e: {Cli.bad_value(r, value) == None{} : Maybe<&2, Cli.Bad>}) ->
    {r == None{} : Maybe<&2, String>}:
  match r:
    case None{}: {==}
    case Some{why}:
      Empty.absurd({Some{why} == None{} : Maybe<&2, String>},
        bad_some_absurd(Cli.Bad{value, why}, e))

def first_reason_none(a: Maybe<&2, String>, b: Maybe<&2, String>,
    e: {Cli.first_reason(a, b) == None{} : Maybe<&2, String>}) ->
    ({a == None{} : Maybe<&2, String>} & {b == None{} : Maybe<&2, String>}):
  match a:
    case None{}: ({==}, e)
    case Some{r}:
      Empty.absurd({Some{r} == None{} : Maybe<&2, String>} &
        {b == None{} : Maybe<&2, String>}, why_some_absurd(r, e))

def or_bad_none(a: Maybe<&2, Cli.Bad>, b: Maybe<&2, Cli.Bad>,
    e: {Maybe.or(&2, Cli.Bad, a, b) == None{} : Maybe<&2, Cli.Bad>}) ->
    ({a == None{} : Maybe<&2, Cli.Bad>} & {b == None{} : Maybe<&2, Cli.Bad>}):
  match a:
    case None{}: ({==}, e)
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, Cli.Bad>} &
        {b == None{} : Maybe<&2, Cli.Bad>}, bad_some_absurd(x, e))

def pick_none_true(b: Bool, -why: String,
    e: {Bool.pick(Maybe<&2, String>, b, None{}, Some{why}) == None{}
      : Maybe<&2, String>}) -> {b == True{} : Bool}:
  match b:
    case True{}: {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, why_some_absurd(why, e))

# A value its type gives no reason against reads under the type's stem.
def typed_ok(found: Maybe<&2, Cli.ValueType>, +value: String,
    e: {Cli.reason_from_type(found, value) == None{} : Maybe<&2, String>}) ->
    {Laws.read_typed(Cli.type_stem(found), value) == True{} : Bool}:
  match found:
    case None{}: {==}
    case Some{t}:
      match t:
        case Cli.TNat{}:
          pick_none_true(Cli.valid_nat(value),
            "expected a whole number from 0 to 281474976710655", e)
        case Cli.TU32{}:
          pick_none_true(Cli.valid_u32(value),
            "expected a whole number from 0 to 4294967295", e)
        case Cli.TF32{}:
          pick_none_true(Cli.valid_f32(value), "expected a decimal number", e)
        case Cli.TBool{}:
          pick_none_true(Cli.valid_bool(value), "expected true or false", e)
        case Cli.TFile{}: {==}
        case Cli.TDir{}: {==}

# Each type's sample value reads under its stem.
def typed_sample(found: Maybe<&2, Cli.ValueType>) ->
    {Laws.read_typed(Cli.type_stem(found), Cli.sample_typed(found)) == True{}
      : Bool}:
  match found:
    case None{}: {==}
    case Some{t}:
      match t:
        case Cli.TNat{}: {==}
        case Cli.TU32{}: {==}
        case Cli.TF32{}: {==}
        case Cli.TBool{}: {==}
        case Cli.TFile{}: {==}
        case Cli.TDir{}: {==}

def choice_bad_acc(values: List<&2, String>, +kind: Maybe<&2, Cli.ValueType>,
    acc: Maybe<&2, Cli.Bad>,
    e: {Cli.choice_bad(values, kind, acc) == None{} : Maybe<&2, Cli.Bad>}) ->
    {acc == None{} : Maybe<&2, Cli.Bad>}:
  match values acc:
    case Nil{} hit: e
    case value <> tail None{}: {==}
    case value <> tail Some{hit}:
      Empty.absurd({Some{hit} == None{} : Maybe<&2, Cli.Bad>},
        bad_some_absurd(hit, e))

# The first one_of value, which the sample takes, reads under the stem.
def choice_ok(found: Maybe<&2, List<&2, String>>, +attrs: List<&2, Cli.Item>,
    ok: ChoicesOk(found, Cli.find_as(attrs))) ->
    {Laws.read_typed(Cli.type_stem(Cli.find_as(attrs)),
      Cli.sample_choice(found, attrs)) == True{} : Bool}:
  match found:
    case None{}: typed_sample(Cli.find_as(attrs))
    case Some{values}:
      match values:
        case Nil{}: typed_sample(Cli.find_as(attrs))
        case +head <> tail:
          typed_ok(Cli.find_as(attrs), head,
            bad_value_none(Cli.reason_from_type(Cli.find_as(attrs), head),
              head, choice_bad_acc(tail, Cli.find_as(attrs),
                Cli.bad_value(Cli.reason_from_type(Cli.find_as(attrs), head),
                  head), ok)))

def value_reason_ok(+attrs: List<&2, Cli.Item>, +value: String,
    e: {Cli.value_reason(attrs, value) == None{} : Maybe<&2, String>}) ->
    {Laws.read_typed(Cli.type_stem(Cli.find_as(attrs)), value) == True{}
      : Bool}:
  typed_ok(Cli.find_as(attrs), value,
    Pair.fst({Cli.reason_from_type(Cli.find_as(attrs), value) == None{}
      : Maybe<&2, String>},
      {Cli.choice_reason(Cli.find_one_of(attrs), value) == None{}
        : Maybe<&2, String>},
      first_reason_none(Cli.reason_from_type(Cli.find_as(attrs), value),
        Cli.choice_reason(Cli.find_one_of(attrs), value), e)))

def first_bad_ok(values: List<&2, String>, +attrs: List<&2, Cli.Item>,
    e: {Cli.first_bad(values, attrs) == None{} : Maybe<&2, Cli.Bad>}) ->
    {Laws.read_all(values, Cli.type_stem(Cli.find_as(attrs))) == True{}
      : Bool}:
  match values:
    case Nil{}: {==}
    case +head <> +tail:
      pair_elim({Cli.bad_value(Cli.value_reason(attrs, head), head) == None{}
        : Maybe<&2, Cli.Bad>},
        {Cli.first_bad(tail, attrs) == None{} : Maybe<&2, Cli.Bad>},
        {Laws.read_all(head <> tail, Cli.type_stem(Cli.find_as(attrs)))
          == True{} : Bool},
        or_bad_none(Cli.bad_value(Cli.value_reason(attrs, head), head),
          Cli.first_bad(tail, attrs), e),
        eh => et => and_true(
          Laws.read_typed(Cli.type_stem(Cli.find_as(attrs)), head),
          Laws.read_all(tail, Cli.type_stem(Cli.find_as(attrs))),
          value_reason_ok(attrs, head,
            bad_value_none(Cli.value_reason(attrs, head), head, eh)),
          first_bad_ok(tail, attrs, et)))

# P21 sample core: per want, then per default and kind, the arg's values
# read well once its verdict passes.

def Core(+want: Cli.Want, +id: String, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, found: Maybe<&2, String>) -> Type:
  {Laws.read_at(Cli.want_verdict(want, id, kind, attrs), want,
    default_vals(found, kind, attrs)) == True{} : Bool}

def not_both(b: Bool, e: {b == True{} : Bool},
    n: {Bool.not(b) == True{} : Bool}) -> Empty:
  match b:
    case True{}: false_true_absurd(n)
    case False{}: false_true_absurd(e)

def read_at_any(x: Maybe<&2, String>, -w: Cli.Want, -vals: List<&2, String>,
    g: {Laws.read_good(w, vals) == True{} : Bool}) ->
    {Laws.read_at(x, w, vals) == True{} : Bool}:
  match x:
    case None{}: g
    case Some{msg}: {==}

def flag_text(b: Bool) ->
    {Laws.read_good(Cli.WFlag{}, [Cli.bool_text(b)]) == True{} : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def flag_core(found: Maybe<&2, String>, kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +id: String) ->
    Core(Cli.WFlag{}, id, kind, attrs, found):
  match found:
    case None{}:
      match kind:
        case Cli.FlagKind{}: {==}
        case Cli.CountKind{}: {==}
        case Cli.NegatableKind{}: {==}
        case Cli.OptionKind{many}: {==}
        case Cli.BareOptionKind{}: {==}
        case Cli.PosKind{required, many}: {==}
    case Some{value}:
      match kind:
        case Cli.FlagKind{}: flag_text(Cli.env_bool_true(value))
        case Cli.CountKind{}: {==}
        case Cli.NegatableKind{}: flag_text(Cli.env_bool_true(value))
        case Cli.OptionKind{many}: {==}
        case Cli.BareOptionKind{}: {==}
        case Cli.PosKind{required, many}: {==}

def count_core(found: Maybe<&2, String>, kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +id: String,
    okd: DefaultOk(found, kind, attrs)) ->
    Core(Cli.WCount{}, id, kind, attrs, found):
  match found:
    case None{}:
      match kind:
        case Cli.FlagKind{}: {==}
        case Cli.CountKind{}: {==}
        case Cli.NegatableKind{}: {==}
        case Cli.OptionKind{many}: {==}
        case Cli.BareOptionKind{}: {==}
        case Cli.PosKind{required, many}: {==}
    case Some{+value}:
      match kind:
        case Cli.FlagKind{}: {==}
        case Cli.CountKind{}:
          Empty.absurd(Core(Cli.WCount{}, id, Cli.CountKind{}, attrs,
            Some{value}), false_true_absurd(Pair.fst({False{} == True{} : Bool},
              {Cli.value_issue(Cli.CountKind{}, attrs, value) == None{}
                : Maybe<&2, Cli.Bad>}, okd)))
        case Cli.NegatableKind{}: {==}
        case Cli.OptionKind{many}: {==}
        case Cli.BareOptionKind{}: {==}
        case Cli.PosKind{required, many}: {==}

def DelimMany(found: Maybe<&2, Char>, many: Bool) -> Type:
  match found:
    case None{}: Unit
    case Some{sep}: {many == True{} : Bool}

def delim_many(found: Maybe<&2, Char>, kind: Cli.UsageKind,
    ok: DelimOk(found, kind)) -> DelimMany(found, Cli.kind_many(kind)):
  match found:
    case None{}: ok
    case Some{sep}:
      match kind:
        case Cli.FlagKind{}: ok
        case Cli.CountKind{}: ok
        case Cli.NegatableKind{}: ok
        case Cli.OptionKind{many}: ok
        case Cli.BareOptionKind{}: ok
        case Cli.PosKind{required, many}: ok

def typed_eq(+stem: String, +t: String, -value: String,
    es: {String.eq(stem, t) == True{} : Bool},
    r: {Laws.read_typed(t, value) == True{} : Bool}) ->
    {Laws.read_typed(stem, value) == True{} : Bool}:
  %Equal.sym(String, stem, t, eq_reflect(stem, t, es)) :
    {Laws.read_typed(_, value) == True{} : Bool}
  r

def one_form(form: Cli.Form, -value: String) ->
    {Laws.read_form(form, [value]) == True{} : Bool}:
  match form:
    case Cli.ReadOne{}: {==}
    case Cli.ReadOpt{}: {==}
    case Cli.ReadMany{}: {==}

def one_good(+form: Cli.Form, +stem: String, +t: String, +value: String,
    es: {String.eq(stem, t) == True{} : Bool},
    r: {Laws.read_typed(t, value) == True{} : Bool}) ->
    {Laws.read_good(Cli.WValue{stem, form}, [value]) == True{} : Bool}:
  and_true(Laws.read_all([value], stem), Laws.read_form(form, [value]),
    and_true(Laws.read_typed(stem, value), True{},
      typed_eq(stem, t, value, es, r), {==}),
    one_form(form, value))

def all_eq(+stem: String, +t: String, +xs: List<&2, String>,
    es: {String.eq(stem, t) == True{} : Bool},
    r: {Laws.read_all(xs, t) == True{} : Bool}) ->
    {Laws.read_all(List.append(&2, String, xs, Nil{}), stem) == True{}
      : Bool}:
  %Equal.sym(List<&2, String>, List.append(&2, String, xs, Nil{}), xs,
    list_append_nil(xs)) : {Laws.read_all(_, stem) == True{} : Bool}
  %Equal.sym(String, stem, t, eq_reflect(stem, t, es)) :
    {Laws.read_all(xs, _) == True{} : Bool}
  r

def split_good(form: Cli.Form, +many: Bool, +stem: String, +t: String,
    +xs: List<&2, String>, okl: {many == True{} : Bool},
    es: {String.eq(stem, t) == True{} : Bool},
    ef: {Cli.form_fits(form, many) == True{} : Bool},
    r: {Laws.read_all(xs, t) == True{} : Bool}) ->
    {Laws.read_good(Cli.WValue{stem, form},
      List.append(&2, String, xs, Nil{})) == True{} : Bool}:
  match form:
    case Cli.ReadOne{}:
      Empty.absurd({Laws.read_good(Cli.WValue{stem, Cli.ReadOne{}},
        List.append(&2, String, xs, Nil{})) == True{} : Bool},
        not_both(many, okl, ef))
    case Cli.ReadOpt{}:
      Empty.absurd({Laws.read_good(Cli.WValue{stem, Cli.ReadOpt{}},
        List.append(&2, String, xs, Nil{})) == True{} : Bool},
        not_both(many, okl, ef))
    case Cli.ReadMany{}:
      and_true(Laws.read_all(List.append(&2, String, xs, Nil{}), stem), True{},
        all_eq(stem, t, xs, es, r), {==})

def def_good(found: Maybe<&2, Char>, +form: Cli.Form, +many: Bool,
    +stem: String, +attrs: List<&2, Cli.Item>, +value: String,
    okl: DelimMany(found, many),
    iss: {Cli.split_bad(found, attrs, value) == None{} : Maybe<&2, Cli.Bad>},
    es: {String.eq(stem, Cli.type_stem(Cli.find_as(attrs))) == True{} : Bool},
    ef: {Cli.form_fits(form, many) == True{} : Bool}) ->
    {Laws.read_good(Cli.WValue{stem, form}, Cli.apply_delim(found, [value]))
      == True{} : Bool}:
  match found:
    case None{}:
      one_good(form, stem, Cli.type_stem(Cli.find_as(attrs)), value, es,
        value_reason_ok(attrs, value,
          bad_value_none(Cli.value_reason(attrs, value), value, iss)))
    case Some{+sep}:
      split_good(form, many, stem, Cli.type_stem(Cli.find_as(attrs)),
        String.split(value, sep), okl, es, ef,
        first_bad_ok(String.split(value, sep), attrs, iss))

def value_at(a: Bool, x: Maybe<&2, String>, -id: String,
    -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>, -w: Cli.Want,
    -vals: List<&2, String>,
    g: {a == True{} : Bool} -> {Laws.read_good(w, vals) == True{} : Bool}) ->
    {Laws.read_at(Maybe.or(&2, String, Cli.kind_verdict(a, id, kind, attrs),
      x), w, vals) == True{} : Bool}:
  match a:
    case True{}: read_at_any(x, w, vals, g({==}))
    case False{}: {==}

def value_valued(+kind: Cli.UsageKind, +stem: String, +form: Cli.Form,
    +attrs: List<&2, Cli.Item>, +id: String, vals: List<&2, String>,
    g: {Cli.value_fits(stem, form, kind, attrs) == True{} : Bool} ->
      {Laws.read_good(Cli.WValue{stem, form}, vals) == True{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(Cli.WValue{stem, form}, id, kind, attrs),
      Cli.WValue{stem, form}, vals) == True{} : Bool}:
  value_at(Cli.value_fits(stem, form, kind, attrs),
    Cli.absent_verdict(Bool.and(Cli.form_one(form), Cli.may_absent(kind,
      attrs)), id, stem), id, kind, attrs, Cli.WValue{stem, form}, vals, g)

def value_core(found: Maybe<&2, String>, kind: Cli.UsageKind, +stem: String,
    +form: Cli.Form, +attrs: List<&2, Cli.Item>, +id: String,
    okd: DefaultOk(found, kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    okc: ChoicesOk(Cli.find_one_of(attrs), Cli.find_as(attrs))) ->
    Core(Cli.WValue{stem, form}, id, kind, attrs, found):
  match found:
    case None{}:
      match kind:
        case Cli.FlagKind{}: {==}
        case Cli.CountKind{}: {==}
        case Cli.NegatableKind{}: {==}
        case Cli.OptionKind{+many}:
          value_valued(Cli.OptionKind{many}, stem, form, attrs, id,
            [Cli.sample_choice(Cli.find_one_of(attrs), attrs)],
            ea => one_good(form, stem, Cli.type_stem(Cli.find_as(attrs)),
              Cli.sample_choice(Cli.find_one_of(attrs), attrs),
              and_left(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, many), ea),
              choice_ok(Cli.find_one_of(attrs), attrs, okc)))
        case Cli.BareOptionKind{}:
          value_valued(Cli.BareOptionKind{}, stem, form, attrs, id,
            [Cli.sample_choice(Cli.find_one_of(attrs), attrs)],
            ea => one_good(form, stem, Cli.type_stem(Cli.find_as(attrs)),
              Cli.sample_choice(Cli.find_one_of(attrs), attrs),
              and_left(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, False{}), ea),
              choice_ok(Cli.find_one_of(attrs), attrs, okc)))
        case Cli.PosKind{+required, +many}:
          value_valued(Cli.PosKind{required, many}, stem, form, attrs, id,
            [Cli.sample_choice(Cli.find_one_of(attrs), attrs)],
            ea => one_good(form, stem, Cli.type_stem(Cli.find_as(attrs)),
              Cli.sample_choice(Cli.find_one_of(attrs), attrs),
              and_left(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, many), ea),
              choice_ok(Cli.find_one_of(attrs), attrs, okc)))
    case Some{+value}:
      match kind:
        case Cli.FlagKind{}: {==}
        case Cli.CountKind{}: {==}
        case Cli.NegatableKind{}: {==}
        case Cli.OptionKind{+many}:
          value_valued(Cli.OptionKind{many}, stem, form, attrs, id,
            Cli.apply_delim(Cli.find_delim(attrs), [value]),
            +ea => def_good(Cli.find_delim(attrs), form, many, stem, attrs,
              value, delim_many(Cli.find_delim(attrs), Cli.OptionKind{many},
                okl),
              Pair.snd({True{} == True{} : Bool},
                {Cli.split_bad(Cli.find_delim(attrs), attrs, value) == None{}
                  : Maybe<&2, Cli.Bad>}, okd),
              and_left(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, many), ea),
              and_right(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, many), ea)))
        case Cli.BareOptionKind{}:
          value_valued(Cli.BareOptionKind{}, stem, form, attrs, id,
            Cli.apply_delim(Cli.find_delim(attrs), [value]),
            +ea => def_good(Cli.find_delim(attrs), form, False{}, stem, attrs,
              value, delim_many(Cli.find_delim(attrs), Cli.BareOptionKind{},
                okl),
              Pair.snd({True{} == True{} : Bool},
                {Cli.split_bad(Cli.find_delim(attrs), attrs, value) == None{}
                  : Maybe<&2, Cli.Bad>}, okd),
              and_left(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, False{}), ea),
              and_right(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, False{}), ea)))
        case Cli.PosKind{+required, +many}:
          value_valued(Cli.PosKind{required, many}, stem, form, attrs, id,
            Cli.apply_delim(Cli.find_delim(attrs), [value]),
            +ea => def_good(Cli.find_delim(attrs), form, many, stem, attrs,
              value, delim_many(Cli.find_delim(attrs),
                Cli.PosKind{required, many}, okl),
              Pair.snd({Bool.not(required) == True{} : Bool},
                {Cli.split_bad(Cli.find_delim(attrs), attrs, value) == None{}
                  : Maybe<&2, Cli.Bad>}, okd),
              and_left(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, many), ea),
              and_right(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
                Cli.form_fits(form, many), ea)))

def choose_tail(x: Maybe<&2, String>, y: Maybe<&2, String>, -w: Cli.Want,
    -vals: List<&2, String>,
    g: {y == None{} : Maybe<&2, String>} ->
      {Laws.read_good(w, vals) == True{} : Bool}) ->
    {Laws.read_at(Maybe.or(&2, String, x, y), w, vals) == True{} : Bool}:
  match x y:
    case Some{m} _: {==}
    case None{} Some{m}: {==}
    case None{} None{}: g({==})

def choose_at(a: Bool, x: Maybe<&2, String>, y: Maybe<&2, String>,
    -id: String, -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>,
    -w: Cli.Want, -vals: List<&2, String>,
    g: {a == True{} : Bool} -> {y == None{} : Maybe<&2, String>} ->
      {Laws.read_good(w, vals) == True{} : Bool}) ->
    {Laws.read_at(Maybe.or(&2, String, Cli.kind_verdict(a, id, kind, attrs),
      Maybe.or(&2, String, x, y)), w, vals) == True{} : Bool}:
  match a:
    case True{}: choose_tail(x, y, w, vals, g({==}))
    case False{}: {==}

def choose_valued(+kind: Cli.UsageKind, +opt: Bool, +keys: List<&2, String>,
    +attrs: List<&2, Cli.Item>, +id: String, vals: List<&2, String>,
    g: {Cli.choose_fits(kind, attrs) == True{} : Bool} ->
      {Cli.keys_verdict(Cli.find_one_of(attrs), keys, id) == None{}
        : Maybe<&2, String>} ->
      {Laws.read_good(Cli.WChoose{opt, keys}, vals) == True{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(Cli.WChoose{opt, keys}, id, kind, attrs),
      Cli.WChoose{opt, keys}, vals) == True{} : Bool}:
  choose_at(Cli.choose_fits(kind, attrs),
    Cli.absent_verdict(Bool.and(Bool.not(opt), Cli.may_absent(kind, attrs)),
      id, "choose"),
    Cli.keys_verdict(Cli.find_one_of(attrs), keys, id), id, kind, attrs,
    Cli.WChoose{opt, keys}, vals, g)

def choose_one(opt: Bool, +keys: List<&2, String>, +value: String,
    ec: {List.contains(~String, ~String.eq, keys, value) == True{} : Bool}) ->
    {Laws.read_good(Cli.WChoose{opt, keys}, [value]) == True{} : Bool}:
  match opt:
    case True{}:
      and_true(List.contains(~String, ~String.eq, keys, value), True{}, ec,
        {==})
    case False{}:
      and_true(List.contains(~String, ~String.eq, keys, value), True{}, ec,
        {==})

def keys_none(b: Bool, -id: String,
    e: {Cli.keys_issue(b, id) == None{} : Maybe<&2, String>}) ->
    {b == True{} : Bool}:
  match b:
    case True{}: {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool},
        why_some_absurd(String.concat(["choose table for '", id,
          "' does not match its values"]), e))

def all_keys(+values: List<&2, String>, +keys: List<&2, String>,
    +id: String,
    e: {Cli.keys_verdict(Some{values}, keys, id) == None{}
      : Maybe<&2, String>}) -> {Cli.all_in(values, keys) == True{} : Bool}:
  and_right(Cli.all_in(keys, values), Cli.all_in(values, keys),
    and_right(Bool.not(List.is_empty(&2, String, keys)),
      Bool.and(Cli.all_in(keys, values), Cli.all_in(values, keys)),
      keys_none(Bool.and(Bool.not(List.is_empty(&2, String, keys)),
        Bool.and(Cli.all_in(keys, values), Cli.all_in(values, keys))), id, e)))

def keys_nil_absurd(keys: List<&2, String>,
    e: {Bool.and(Bool.not(List.is_empty(&2, String, keys)),
      Bool.and(Cli.all_in(keys, Nil{}), Cli.all_in(Nil{}, keys))) == True{}
      : Bool}) -> Empty:
  match keys:
    case Nil{}: false_true_absurd(e)
    case key <> tail: false_true_absurd(e)

def keys_contains_step(b: Bool, +head: String, tail: List<&2, String>,
    +keys: List<&2, String>, +value: String,
    eb: {String.eq(head, value) == b : Bool},
    ec: {List.any.if(u => List.contains(~String, ~String.eq, tail, value), b)
      == True{} : Bool},
    ea: {Bool.and(List.contains(~String, ~String.eq, keys, head),
      Cli.all_in(tail, keys)) == True{} : Bool},
    ih: {List.contains(~String, ~String.eq, tail, value) == True{} : Bool} ->
      {Cli.all_in(tail, keys) == True{} : Bool} ->
      {List.contains(~String, ~String.eq, keys, value) == True{} : Bool}) ->
    {List.contains(~String, ~String.eq, keys, value) == True{} : Bool}:
  match b:
    case True{}:
      %eq_reflect(head, value, eb) :
        {List.contains(~String, ~String.eq, keys, _) == True{} : Bool}
      and_left(List.contains(~String, ~String.eq, keys, head),
        Cli.all_in(tail, keys), ea)
    case False{}:
      ih(ec, and_right(List.contains(~String, ~String.eq, keys, head),
        Cli.all_in(tail, keys), ea))

def contains_trans(values: List<&2, String>, +keys: List<&2, String>,
    +value: String,
    ec: {List.contains(~String, ~String.eq, values, value) == True{} : Bool},
    ea: {Cli.all_in(values, keys) == True{} : Bool}) ->
    {List.contains(~String, ~String.eq, keys, value) == True{} : Bool}:
  match values:
    case Nil{}:
      Empty.absurd({List.contains(~String, ~String.eq, keys, value) == True{}
        : Bool}, false_true_absurd(ec))
    case +head <> +tail:
      keys_contains_step(String.eq(head, value), head, tail, keys, value, {==}, ec,
        ea, ec2 => ea2 => contains_trans(tail, keys, value, ec2, ea2))

def choose_list(values: List<&2, String>, +opt: Bool, +keys: List<&2, String>,
    -attrs: List<&2, Cli.Item>, +id: String,
    ey: {Cli.keys_verdict(Some{values}, keys, id) == None{}
      : Maybe<&2, String>}) ->
    {Laws.read_good(Cli.WChoose{opt, keys},
      [Cli.sample_choice(Some{values}, attrs)]) == True{} : Bool}:
  match values:
    case Nil{}:
      Empty.absurd({Laws.read_good(Cli.WChoose{opt, keys},
        [Cli.sample_choice(Some{Nil{}}, attrs)]) == True{} : Bool},
        keys_nil_absurd(keys, keys_none(Bool.and(Bool.not(
          List.is_empty(&2, String, keys)), Bool.and(Cli.all_in(keys, Nil{}),
            Cli.all_in(Nil{}, keys))), id, ey)))
    case +head <> +tail:
      choose_one(opt, keys, head,
        and_left(List.contains(~String, ~String.eq, keys, head),
          Cli.all_in(tail, keys), all_keys(head <> tail, keys, id, ey)))

def choose_none(found: Maybe<&2, List<&2, String>>, +opt: Bool,
    +keys: List<&2, String>, -attrs: List<&2, Cli.Item>, +id: String,
    es: {Maybe.is_some(&2, List<&2, String>, found) == True{} : Bool},
    ey: {Cli.keys_verdict(found, keys, id) == None{} : Maybe<&2, String>}) ->
    {Laws.read_good(Cli.WChoose{opt, keys},
      [Cli.sample_choice(found, attrs)]) == True{} : Bool}:
  match found:
    case None{}:
      Empty.absurd({Laws.read_good(Cli.WChoose{opt, keys},
        [Cli.sample_choice(None{}, attrs)]) == True{} : Bool},
        false_true_absurd(es))
    case Some{values}: choose_list(values, opt, keys, attrs, id, ey)

def choice_in(found: Maybe<&2, List<&2, String>>, +keys: List<&2, String>,
    +id: String, +value: String,
    es: {Maybe.is_some(&2, List<&2, String>, found) == True{} : Bool},
    ec: {Cli.choice_reason(found, value) == None{} : Maybe<&2, String>},
    ey: {Cli.keys_verdict(found, keys, id) == None{} : Maybe<&2, String>}) ->
    {List.contains(~String, ~String.eq, keys, value) == True{} : Bool}:
  match found:
    case None{}:
      Empty.absurd({List.contains(~String, ~String.eq, keys, value) == True{}
        : Bool}, false_true_absurd(es))
    case Some{+values}:
      contains_trans(values, keys, value,
        pick_none_true(List.contains(~String, ~String.eq, values, value),
          Cli.choices_reason(values), ec),
        all_keys(values, keys, id, ey))

def choose_def(found: Maybe<&2, Char>, +many: Bool, +opt: Bool,
    +keys: List<&2, String>, +attrs: List<&2, Cli.Item>, +id: String,
    +value: String, okl: DelimMany(found, many),
    en: {Bool.not(many) == True{} : Bool},
    iss: {Cli.split_bad(found, attrs, value) == None{} : Maybe<&2, Cli.Bad>},
    es: {Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs)) == True{}
      : Bool},
    ey: {Cli.keys_verdict(Cli.find_one_of(attrs), keys, id) == None{}
      : Maybe<&2, String>}) ->
    {Laws.read_good(Cli.WChoose{opt, keys}, Cli.apply_delim(found, [value]))
      == True{} : Bool}:
  match found:
    case None{}:
      choose_one(opt, keys, value,
        choice_in(Cli.find_one_of(attrs), keys, id, value, es,
          Pair.snd({Cli.reason_from_type(Cli.find_as(attrs), value) == None{}
            : Maybe<&2, String>},
            {Cli.choice_reason(Cli.find_one_of(attrs), value) == None{}
              : Maybe<&2, String>},
            first_reason_none(Cli.reason_from_type(Cli.find_as(attrs), value),
              Cli.choice_reason(Cli.find_one_of(attrs), value),
              bad_value_none(Cli.value_reason(attrs, value), value, iss))),
          ey))
    case Some{sep}:
      Empty.absurd({Laws.read_good(Cli.WChoose{opt, keys},
        Cli.apply_delim(Some{sep}, [value])) == True{} : Bool},
        not_both(many, okl, en))

def value_none_choose(+kind: Cli.UsageKind, +opt: Bool,
    +keys: List<&2, String>, +attrs: List<&2, Cli.Item>, +id: String,
    some: {Cli.choose_fits(kind, attrs) == True{} : Bool} ->
      {Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs)) == True{}
        : Bool}) ->
    {Laws.read_at(Cli.want_verdict(Cli.WChoose{opt, keys}, id, kind, attrs),
      Cli.WChoose{opt, keys}, [Cli.sample_choice(Cli.find_one_of(attrs),
        attrs)]) == True{} : Bool}:
  choose_valued(kind, opt, keys, attrs, id,
    [Cli.sample_choice(Cli.find_one_of(attrs), attrs)],
    ea => ey => choose_none(Cli.find_one_of(attrs), opt, keys, attrs, id,
      some(ea), ey))

def choose_core(found: Maybe<&2, String>, kind: Cli.UsageKind, +opt: Bool,
    +keys: List<&2, String>, +attrs: List<&2, Cli.Item>, +id: String,
    okd: DefaultOk(found, kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind)) ->
    Core(Cli.WChoose{opt, keys}, id, kind, attrs, found):
  match found:
    case None{}:
      match kind:
        case Cli.FlagKind{}: {==}
        case Cli.CountKind{}: {==}
        case Cli.NegatableKind{}: {==}
        case Cli.OptionKind{+many}:
          value_none_choose(Cli.OptionKind{many}, opt, keys,
            attrs, id, ea => and_right(Bool.not(many),
              Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs)), ea))
        case Cli.BareOptionKind{}:
          value_none_choose(Cli.BareOptionKind{}, opt, keys, attrs, id,
            ea => and_right(True{},
              Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs)), ea))
        case Cli.PosKind{+required, +many}:
          value_none_choose(Cli.PosKind{required, many}, opt,
            keys, attrs, id, ea => and_right(Bool.not(many),
              Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs)), ea))
    case Some{+value}:
      match kind:
        case Cli.FlagKind{}: {==}
        case Cli.CountKind{}: {==}
        case Cli.NegatableKind{}: {==}
        case Cli.OptionKind{+many}:
          choose_valued(Cli.OptionKind{many}, opt, keys, attrs, id,
            Cli.apply_delim(Cli.find_delim(attrs), [value]),
            +ea => ey => choose_def(Cli.find_delim(attrs), many, opt, keys,
              attrs, id, value,
              delim_many(Cli.find_delim(attrs), Cli.OptionKind{many}, okl),
              and_left(Bool.not(many), Maybe.is_some(&2, List<&2, String>,
                Cli.find_one_of(attrs)), ea),
              Pair.snd({True{} == True{} : Bool},
                {Cli.split_bad(Cli.find_delim(attrs), attrs, value) == None{}
                  : Maybe<&2, Cli.Bad>}, okd),
              and_right(Bool.not(many), Maybe.is_some(&2, List<&2, String>,
                Cli.find_one_of(attrs)), ea), ey))
        case Cli.BareOptionKind{}:
          choose_valued(Cli.BareOptionKind{}, opt, keys, attrs, id,
            Cli.apply_delim(Cli.find_delim(attrs), [value]),
            ea => ey => choose_def(Cli.find_delim(attrs), False{}, opt, keys,
              attrs, id, value,
              delim_many(Cli.find_delim(attrs), Cli.BareOptionKind{}, okl),
              {==},
              Pair.snd({True{} == True{} : Bool},
                {Cli.split_bad(Cli.find_delim(attrs), attrs, value) == None{}
                  : Maybe<&2, Cli.Bad>}, okd),
              ea, ey))
        case Cli.PosKind{+required, +many}:
          choose_valued(Cli.PosKind{required, many}, opt, keys, attrs, id,
            Cli.apply_delim(Cli.find_delim(attrs), [value]),
            +ea => ey => choose_def(Cli.find_delim(attrs), many, opt, keys,
              attrs, id, value,
              delim_many(Cli.find_delim(attrs), Cli.PosKind{required, many},
                okl),
              and_left(Bool.not(many), Maybe.is_some(&2, List<&2, String>,
                Cli.find_one_of(attrs)), ea),
              Pair.snd({Bool.not(required) == True{} : Bool},
                {Cli.split_bad(Cli.find_delim(attrs), attrs, value) == None{}
                  : Maybe<&2, Cli.Bad>}, okd),
              and_right(Bool.not(many), Maybe.is_some(&2, List<&2, String>,
                Cli.find_one_of(attrs)), ea), ey))

def core(want: Cli.Want, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +id: String, okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    okc: ChoicesOk(Cli.find_one_of(attrs), Cli.find_as(attrs))) ->
    Core(want, id, kind, attrs, Cli.find_default(attrs)):
  match want:
    case Cli.WFlag{}: flag_core(Cli.find_default(attrs), kind, attrs, id)
    case Cli.WCount{}:
      count_core(Cli.find_default(attrs), kind, attrs, id, okd)
    case Cli.WValue{stem, form}:
      value_core(Cli.find_default(attrs), kind, stem, form, attrs, id, okd,
        okl, okc)
    case Cli.WAny{}: {==}
    case Cli.WChoose{opt, keys}:
      choose_core(Cli.find_default(attrs), kind, opt, keys, attrs, id, okd,
        okl)

# P21 sample lint: lint's lists, rewritten by issue_list, sub_list and
# top_list, give each Arg below the root its facts (DeepClean).

def plist_disc(l: List<&2, Cli.Problem>) -> Data:
  match l:
    case Nil{}: Empty
    case h <> t: Unit

def plist_cons_absurd(-h: Cli.Problem, -t: List<&2, Cli.Problem>,
    e: {h <> t == Nil{} : List<&2, Cli.Problem>}) -> Empty:
  %e : plist_disc(_)
  Unit{}

def app_nil_left(a: List<&2, Cli.Problem>, -b: List<&2, Cli.Problem>,
    e: {List.append(&2, Cli.Problem, a, b) == Nil{}
      : List<&2, Cli.Problem>}) -> {a == Nil{} : List<&2, Cli.Problem>}:
  match a:
    case Nil{}: {==}
    case h <> t:
      Empty.absurd({h <> t == Nil{} : List<&2, Cli.Problem>},
        plist_cons_absurd(h, List.append(&2, Cli.Problem, t, b), e))

def app_nil_right(a: List<&2, Cli.Problem>, -b: List<&2, Cli.Problem>,
    e: {List.append(&2, Cli.Problem, a, b) == Nil{}
      : List<&2, Cli.Problem>}) -> {b == Nil{} : List<&2, Cli.Problem>}:
  match a:
    case Nil{}: e
    case h <> t:
      Empty.absurd({b == Nil{} : List<&2, Cli.Problem>},
        plist_cons_absurd(h, List.append(&2, Cli.Problem, t, b), e))

def AllNil(xss: List<&2, List<&2, Cli.Problem>>) -> Type:
  match xss:
    case Nil{}: Unit
    case h <> t: {h == Nil{} : List<&2, Cli.Problem>} & AllNil(t)

def concat_all(xss: List<&2, List<&2, Cli.Problem>>,
    +e: {List.concat(&2, Cli.Problem, xss) == Nil{} : List<&2, Cli.Problem>}) ->
    AllNil(xss):
  match xss:
    case Nil{}: Unit{}
    case +h <> +t:
      (app_nil_left(h, List.concat(&2, Cli.Problem, t), e),
        concat_all(t, app_nil_right(h, List.concat(&2, Cli.Problem, t), e)))

def misplaced_none(b: Bool, -name: String, -at: String,
    e: {Cli.maybe_misplaced(Cli.bad_attr(b, name), at) == Nil{}
      : List<&2, Cli.Problem>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        plist_cons_absurd(Cli.Misplaced{at, name}, Nil{}, e))
    case False{}: {==}

def not_false(b: Bool, e: {Bool.not(b) == False{} : Bool}) ->
    {b == True{} : Bool}:
  match b:
    case True{}: {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, true_false_absurd(e))

def DefaultKind(found: Maybe<&2, String>, kind: Cli.UsageKind) -> Type:
  match found:
    case None{}: Unit
    case Some{value}: {Cli.kind_default_allowed(kind) == True{} : Bool}

def def_place(attrs: List<&2, Cli.Item>, +kind: Cli.UsageKind, +at: String,
    e: {Cli.placement_issues(attrs, kind, at) == Nil{}
      : List<&2, Cli.Problem>}) -> DefaultKind(Cli.find_default(attrs), kind):
  match attrs:
    case Nil{}: Unit{}
    case Cli.AttrDefault{value} <> +tail:
      not_false(Cli.kind_default_allowed(kind),
        misplaced_none(Bool.not(Cli.kind_default_allowed(kind)), "default", at,
          app_nil_left(Cli.maybe_misplaced(Cli.bad_attr(Bool.not(
            Cli.kind_default_allowed(kind)), "default"), at),
            Cli.placement_issues(tail, kind, at), e)))
    case Cli.Arg{x0, x1, x2} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Arg{x0, x1, x2}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Sub{x0, x1, x2} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Sub{x0, x1, x2}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Version{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Version{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Alias{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Alias{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Hidden{} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Hidden{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Example{x0, x1} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Example{x0, x1}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.After{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.After{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.SubOptional{} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.SubOptional{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.External{} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.External{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Exclusive{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Exclusive{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.NeedOne{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.NeedOne{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Id{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Id{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Required{} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Required{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.AttrEnv{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.AttrEnv{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Global{} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Global{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Heading{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Heading{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.As{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.As{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.OneOf{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.OneOf{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Delim{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Delim{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Hyphen{} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Hyphen{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Rest{} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Rest{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Bare{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Bare{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Conflicts{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Conflicts{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Requires{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Requires{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Group{x0} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Group{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Builtin{} <> +tail: def_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Builtin{}, kind), at), Cli.placement_issues(tail, kind, at), e))

def delim_place(attrs: List<&2, Cli.Item>, +kind: Cli.UsageKind, +at: String,
    e: {Cli.placement_issues(attrs, kind, at) == Nil{}
      : List<&2, Cli.Problem>}) -> DelimOk(Cli.find_delim(attrs), kind):
  match attrs:
    case Nil{}: Unit{}
    case Cli.Delim{sep} <> +tail:
      not_false(Cli.kind_delim_allowed(kind),
        misplaced_none(Bool.not(Cli.kind_delim_allowed(kind)), "delim", at,
          app_nil_left(Cli.maybe_misplaced(Cli.bad_attr(Bool.not(
            Cli.kind_delim_allowed(kind)), "delim"), at),
            Cli.placement_issues(tail, kind, at), e)))
    case Cli.Arg{x0, x1, x2} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Arg{x0, x1, x2}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Sub{x0, x1, x2} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Sub{x0, x1, x2}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Version{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Version{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Alias{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Alias{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Hidden{} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Hidden{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Example{x0, x1} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Example{x0, x1}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.After{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.After{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.SubOptional{} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.SubOptional{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.External{} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.External{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Exclusive{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Exclusive{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.NeedOne{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.NeedOne{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Id{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Id{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Required{} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Required{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.AttrDefault{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.AttrDefault{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.AttrEnv{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.AttrEnv{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Global{} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Global{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Heading{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Heading{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.As{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.As{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.OneOf{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.OneOf{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Hyphen{} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Hyphen{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Rest{} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Rest{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Bare{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Bare{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Conflicts{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Conflicts{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Requires{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Requires{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Group{x0} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Group{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Builtin{} <> +tail: delim_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Builtin{}, kind), at), Cli.placement_issues(tail, kind, at), e))

def issue_none(required: Bool, issue: Maybe<&2, Cli.Bad>, -value: String,
    -id: String, -at: String,
    e: {Cli.bad_default(required, issue, value, id, at) == Nil{}
      : List<&2, Cli.Problem>}) -> {issue == None{} : Maybe<&2, Cli.Bad>}:
  match required issue:
    case True{} None{}:
      Empty.absurd({None{} == None{} : Maybe<&2, Cli.Bad>},
        plist_cons_absurd(Cli.BadDefault{at, id, value}, Nil{}, e))
    case True{} Some{b}:
      Empty.absurd({Some{b} == None{} : Maybe<&2, Cli.Bad>},
        plist_cons_absurd(Cli.BadDefault{at, id, value}, Nil{}, e))
    case False{} None{}: {==}
    case False{} Some{Cli.Bad{bad, why}}:
      Empty.absurd({Some{Cli.Bad{bad, why}} == None{} : Maybe<&2, Cli.Bad>},
        plist_cons_absurd(Cli.BadDefault{at, id, bad}, Nil{}, e))

def default_ok(found: Maybe<&2, String>, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, -id: String, -at: String,
    dk: DefaultKind(found, kind),
    cd: {Cli.check_default(found, kind, attrs, id, at) == Nil{}
      : List<&2, Cli.Problem>}) -> DefaultOk(found, kind, attrs):
  match found:
    case None{}: Unit{}
    case Some{+value}:
      (dk, issue_none(Cli.has_required(attrs), Cli.value_issue(kind, attrs,
        value), value, id, at, cd))

def bad_choice_none(m: Maybe<&2, Cli.Bad>, -id: String, -at: String,
    e: {Cli.bad_choice(m, id, at) == Nil{} : List<&2, Cli.Problem>}) ->
    {m == None{} : Maybe<&2, Cli.Bad>}:
  match m:
    case None{}: {==}
    case Some{Cli.Bad{value, why}}:
      Empty.absurd({Some{Cli.Bad{value, why}} == None{} : Maybe<&2, Cli.Bad>},
        plist_cons_absurd(Cli.BadChoice{at, id, value}, Nil{}, e))

def choices_ok(found: Maybe<&2, List<&2, String>>,
    +kind: Maybe<&2, Cli.ValueType>, -id: String, -at: String,
    e: {Cli.check_choices(found, kind, id, at) == Nil{}
      : List<&2, Cli.Problem>}) -> ChoicesOk(found, kind):
  match found:
    case None{}: Unit{}
    case Some{values}:
      bad_choice_none(Cli.choice_bad(values, kind, None{}), id, at, e)

def InfoClean(info: Cli.ArgInfo) -> Type:
  match info:
    case Cli.ArgInfo{id, usage, short, long, +kind, +attrs}:
      DefaultOk(Cli.find_default(attrs), kind, attrs) &
        (DelimOk(Cli.find_delim(attrs), kind) &
          ChoicesOk(Cli.find_one_of(attrs), Cli.find_as(attrs)))

# arg_issues' list, as written there.
def issue_list(+kind: Cli.UsageKind, +id: String, +short: String,
    +long: String, usage: String, help: String, +attrs: List<&2, Cli.Item>,
    remaining: List<&2, Cli.LintItem>, +at: String, ids: List<&2, String>,
    seen: List<&2, Cli.Seen>, optional: Bool, variadic: Bool,
    version: Bool) -> List<&2, List<&2, Cli.Problem>>:
  [
    Cli.arg_reserved_dup(at, long, seen, id, short, version),
    Cli.misplaced_arg(kind, attrs, at),
    Cli.when_problem(Bool.and(String.is_empty(help),
      Bool.not(Cli.has_hidden(attrs))), Cli.NoHelp{at, usage}),
    Cli.check_default(Cli.find_default(attrs), kind, attrs, id, at),
    Cli.missing_refs(List.append(&2, String,
      Cli.find_requires(attrs), Cli.find_conflicts(attrs)), ids, at),
    Cli.positional_issue(kind, id, attrs, remaining, optional, variadic, at),
    Cli.when_problem(Cli.bad_choices(attrs), Cli.BadChoices{at, id}),
    Cli.check_choices(Cli.find_one_of(attrs), Cli.find_as(attrs), id, at),
    Cli.bare_issue(kind, id, short, attrs, at),
  ]

def issue_take(+kind: Cli.UsageKind, +id: String, +short: String,
    +long: String, +usage: String, +help: String, +attrs: List<&2, Cli.Item>,
    +remaining: List<&2, Cli.LintItem>, +at: String, +ids: List<&2, String>,
    +seen: List<&2, Cli.Seen>, +optional: Bool, +variadic: Bool,
    +version: Bool,
    parts: AllNil(issue_list(kind, id, short, long, usage, help, attrs,
      remaining, at, ids, seen, optional, variadic, version))) ->
    InfoClean(Cli.ArgInfo{id, usage, short, long, kind, attrs}):
  (e1, r1) = parts
  (e2, r2) = r1
  (e3, r3) = r2
  (e4, r4) = r3
  (e5, r5) = r4
  (e6, r6) = r5
  (e7, r7) = r6
  (e8, r8) = r7
  +pl = app_nil_left(Cli.placement_issues(attrs, kind, at),
    Cli.duplicate_type_issues(Cli.value_type_names(attrs), at), e2)
  (default_ok(Cli.find_default(attrs), kind, attrs, id, at,
    def_place(attrs, kind, at, pl), e4),
    (delim_place(attrs, kind, at, pl),
      choices_ok(Cli.find_one_of(attrs), Cli.find_as(attrs), id, at, e8)))

def issue_facts(+kind: Cli.UsageKind, +id: String, +short: String,
    +long: String, +usage: String, +help: String, +attrs: List<&2, Cli.Item>,
    +remaining: List<&2, Cli.LintItem>, +at: String, +ids: List<&2, String>,
    +seen: List<&2, Cli.Seen>, +optional: Bool, +variadic: Bool,
    +version: Bool,
    e: {Cli.arg_issues(kind, id, short, long, usage, help, attrs, remaining,
      at, ids, seen, optional, variadic, version) == Nil{}
      : List<&2, Cli.Problem>}) ->
    InfoClean(Cli.ArgInfo{id, usage, short, long, kind, attrs}):
  issue_take(kind, id, short, long, usage, help, attrs, remaining, at, ids,
    seen, optional, variadic, version, concat_all(issue_list(kind, id, short,
      long, usage, help, attrs, remaining, at, ids, seen, optional, variadic,
      version), e))

def arg_clean(parsed: Cli.Usage, +usage: String, +help: String,
    +attrs: List<&2, Cli.Item>, +remaining: List<&2, Cli.LintItem>,
    +at: String, +ids: List<&2, String>, +seen: List<&2, Cli.Seen>,
    +optional: Bool, +variadic: Bool, +version: Bool,
    e: {Cli.arg_problems(parsed, usage, help, attrs, remaining, at, ids, seen,
      optional, variadic, version) == Nil{} : List<&2, Cli.Problem>}) ->
    InfoClean(Cli.arg_info_parsed(parsed, usage, attrs)):
  match parsed:
    case Cli.Invalid{+col}:
      Empty.absurd(InfoClean(Cli.arg_info_parsed(Cli.Invalid{col}, usage,
        attrs)), plist_cons_absurd(Cli.BadUsage{at, usage, col},
          Cli.when_problem(Bool.and(String.is_empty(help),
            Bool.not(Cli.has_hidden(attrs))), Cli.NoHelp{at, usage}), e))
    case Cli.Parsed{+derived, +short, +long, +kind}:
      issue_facts(kind, Cli.use_id(Cli.find_id(attrs), derived), short, long,
        usage, help, attrs, remaining, at, ids, seen, optional, variadic,
        version, app_nil_left(Cli.arg_issues(kind,
          Cli.use_id(Cli.find_id(attrs), derived), short, long, usage, help,
          attrs, remaining, at, ids, seen, optional, variadic, version),
          Cli.arg_alias_issues(Cli.find_aliases(attrs), at,
            Cli.SeenArg{Cli.use_id(Cli.find_id(attrs), derived), short, long}
              <> seen, version), e))

def DeepClean(items: List<&2, Cli.Item>) -> Type:
  match items:
    case Nil{}: Unit
    case Cli.Arg{usage, help, attrs} <> tail:
      InfoClean(Cli.arg_info(usage, attrs)) & DeepClean(tail)
    case Cli.Sub{name, about, children} <> tail:
      DeepClean(children) & DeepClean(tail)
    case head <> tail: DeepClean(tail)

# lint's list for a subcommand, as written there.
def sub_list(+name: String, about: String, +children: List<&2, Cli.Item>,
    +kids: List<&2, Cli.LintItem>, tail_l: List<&2, Cli.LintItem>,
    +at: String, ids: List<&2, String>, +seen: List<&2, Cli.Seen>,
    +inherited: List<&2, Cli.Seen>, optional: Bool, variadic: Bool,
    +version: Bool, root: Bool) -> List<&2, List<&2, Cli.Problem>>:
  +child_at = String.concat([at, " ", name])
  +aliases = Cli.find_aliases(children)
  [
    Cli.sub_name_issues(at, name, seen),
    Cli.sub_alias_issues(aliases, at, Cli.SeenSub{name} <> seen),
    Cli.command_body_issues(child_at, name, about, children,
      Cli.has_pos_item(kids)),
    Cli.lint(kids, child_at, Cli.scope_ids(kids), inherited,
      List.append(&2, Cli.Seen, Cli.global_entries(kids), inherited),
      False{}, False{}, version, False{}),
    Cli.lint(tail_l, at, ids,
      List.append(&2, Cli.Seen, Cli.sub_alias_entries(aliases),
        Cli.SeenSub{name} <> seen),
      inherited, optional, variadic, version, root),
  ]

def sub_take(+name: String, +about: String, +children: List<&2, Cli.Item>,
    +tail: List<&2, Cli.Item>, +at: String, +ids: List<&2, String>,
    +seen: List<&2, Cli.Seen>, +inherited: List<&2, Cli.Seen>,
    +optional: Bool, +variadic: Bool, +version: Bool, +root: Bool,
    parts: AllNil(sub_list(name, about, children, Cli.lint_items(children),
      Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root)),
    ih_c: {Cli.lint(Cli.lint_items(children), String.concat([at, " ", name]), Cli.scope_ids(Cli.lint_items(children)), inherited, List.append(&2, Cli.Seen, Cli.global_entries(Cli.lint_items(children)), inherited), False{}, False{}, version, False{}) == Nil{} : List<&2, Cli.Problem>} ->
      DeepClean(children),
    ih_t: {Cli.lint(Cli.lint_items(tail), at, ids, List.append(&2, Cli.Seen, Cli.sub_alias_entries(Cli.find_aliases(children)), Cli.SeenSub{name} <> seen), inherited, optional, variadic, version, root) == Nil{}
      : List<&2, Cli.Problem>} -> DeepClean(tail)) ->
    (DeepClean(children) & DeepClean(tail)):
  (e1, r1) = parts
  (e2, r2) = r1
  (e3, r3) = r2
  (e4, r4) = r3
  (e5, r5) = r4
  (ih_c(e4), ih_t(e5))

def deep(items: List<&2, Cli.Item>, +at: String, +ids: List<&2, String>,
    +seen: List<&2, Cli.Seen>, +inherited: List<&2, Cli.Seen>,
    +optional: Bool, +variadic: Bool, +version: Bool, +root: Bool,
    +e: {Cli.lint(Cli.lint_items(items), at, ids, seen, inherited, optional, variadic, version, root) == Nil{}
      : List<&2, Cli.Problem>}) -> DeepClean(items):
  match items:
    case Nil{}: Unit{}
    case Cli.Arg{+usage, +help, +attrs} <> +tail:
      (arg_clean(Cli.parse_usage(usage), usage, help, attrs,
        Cli.lint_items(tail), at, ids, seen, optional, variadic, version,
        app_nil_left(Cli.arg_problems(Cli.parse_usage(usage), usage, help, attrs, Cli.lint_items(tail), at, ids, seen, optional, variadic, version), Cli.lint(Cli.lint_items(tail), at, ids, List.append(&2, Cli.Seen, Cli.arg_entries(Cli.parse_usage(usage), attrs), seen), inherited, Bool.or(optional, Cli.usage_kind(~Cli.kind_optional_pos, Cli.parse_usage(usage))), Bool.or(variadic, Cli.usage_kind(~Cli.kind_variadic_pos, Cli.parse_usage(usage))), version, root), e)),
        deep(tail, at, ids, List.append(&2, Cli.Seen, Cli.arg_entries(Cli.parse_usage(usage), attrs), seen), inherited, Bool.or(optional, Cli.usage_kind(~Cli.kind_optional_pos, Cli.parse_usage(usage))), Bool.or(variadic, Cli.usage_kind(~Cli.kind_variadic_pos, Cli.parse_usage(usage))), version, root, app_nil_right(Cli.arg_problems(Cli.parse_usage(usage), usage, help, attrs, Cli.lint_items(tail), at, ids, seen, optional, variadic, version), Cli.lint(Cli.lint_items(tail), at, ids, List.append(&2, Cli.Seen, Cli.arg_entries(Cli.parse_usage(usage), attrs), seen), inherited, Bool.or(optional, Cli.usage_kind(~Cli.kind_optional_pos, Cli.parse_usage(usage))), Bool.or(variadic, Cli.usage_kind(~Cli.kind_variadic_pos, Cli.parse_usage(usage))), version, root), e)))
    case Cli.Sub{+name, +about, +children} <> +tail:
      sub_take(name, about, children, tail, at, ids, seen, inherited, optional, variadic, version, root,
        concat_all(sub_list(name, about, children, Cli.lint_items(children),
          Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e),
        ec => deep(children, String.concat([at, " ", name]), Cli.scope_ids(Cli.lint_items(children)), inherited, List.append(&2, Cli.Seen, Cli.global_entries(Cli.lint_items(children)), inherited), False{}, False{}, version, False{}, ec),
        et => deep(tail, at, ids, List.append(&2, Cli.Seen, Cli.sub_alias_entries(Cli.find_aliases(children)), Cli.SeenSub{name} <> seen), inherited, optional, variadic, version, root, et))
    case Cli.Version{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Version{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Alias{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Alias{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Hidden{} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Hidden{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Example{x0, x1} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Example{x0, x1}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.After{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.After{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.SubOptional{} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.SubOptional{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.External{} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.External{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Exclusive{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Exclusive{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.NeedOne{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.NeedOne{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Id{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Id{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Required{} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Required{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.AttrDefault{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.AttrDefault{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.AttrEnv{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.AttrEnv{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Global{} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Global{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Heading{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Heading{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.As{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.As{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.OneOf{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.OneOf{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Delim{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Delim{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Hyphen{} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Hyphen{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Rest{} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Rest{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Bare{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Bare{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Conflicts{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Conflicts{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Requires{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Requires{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Group{x0} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Group{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Builtin{} <> +tail: deep(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Builtin{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))

# problems' list, as written there.
def top_list(+name: String, about: String, +items: List<&2, Cli.Item>) ->
    List<&2, List<&2, Cli.Problem>>:
  +linted = Cli.lint_items(items)
  [
    Cli.when_problem(Bool.not(Cli.valid_command_name(name)),
      Cli.BadName{name, name}),
    Cli.command_body_issues(name, name, about, items,
      Cli.has_pos_item(linted)),
    Cli.lint(linted, name, Cli.scope_ids(linted), Nil{},
      Cli.global_entries(linted), False{}, False{},
      Cli.has_version_item(items), True{}),
  ]

def top_take(+name: String, +about: String, +items: List<&2, Cli.Item>,
    parts: AllNil(top_list(name, about, items))) -> DeepClean(items):
  (p1, r1) = parts
  (p2, r2) = r1
  (p3, r3) = r2
  deep(items, name, Cli.scope_ids(Cli.lint_items(items)), Nil{},
    Cli.global_entries(Cli.lint_items(items)), False{}, False{},
    Cli.has_version_item(items), True{}, p3)

def lint_clean(+name: String, +about: String, +items: List<&2, Cli.Item>,
    e: {Cli.problems(Cli.Cmd{name, about, items}) == Nil{}
      : List<&2, Cli.Problem>}) -> DeepClean(items):
  top_take(name, about, items, concat_all(top_list(name, about, items), e))

# P21 sample scope: the args in scope at a path keep the facts.

def deep_append(a: List<&2, Cli.Item>, +b: List<&2, Cli.Item>,
    da: DeepClean(a), db: DeepClean(b)) ->
    DeepClean(List.append(&2, Cli.Item, a, b)):
  match a:
    case Nil{}: db
    case Cli.Arg{usage, help, attrs} <> +tail:
      (ic, dt) = da
      (ic, deep_append(tail, b, dt, db))
    case Cli.Sub{name, about, children} <> +tail:
      (dc, dt) = da
      (dc, deep_append(tail, b, dt, db))
    case Cli.Version{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Alias{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Hidden{} <> +tail: deep_append(tail, b, da, db)
    case Cli.Example{x0, x1} <> +tail: deep_append(tail, b, da, db)
    case Cli.After{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.SubOptional{} <> +tail: deep_append(tail, b, da, db)
    case Cli.External{} <> +tail: deep_append(tail, b, da, db)
    case Cli.Exclusive{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.NeedOne{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Id{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Required{} <> +tail: deep_append(tail, b, da, db)
    case Cli.AttrDefault{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.AttrEnv{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Global{} <> +tail: deep_append(tail, b, da, db)
    case Cli.Heading{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.As{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.OneOf{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Delim{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Hyphen{} <> +tail: deep_append(tail, b, da, db)
    case Cli.Rest{} <> +tail: deep_append(tail, b, da, db)
    case Cli.Bare{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Conflicts{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Requires{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Group{x0} <> +tail: deep_append(tail, b, da, db)
    case Cli.Builtin{} <> +tail: deep_append(tail, b, da, db)

# A rule global_go may keep adds no arg.
def deep_rule_pick(c: Bool, -r: Cli.Item, -rest: List<&2, Cli.Item>,
    d: DeepClean(rest), k: DeepClean(rest) -> DeepClean(r <> rest)) ->
    DeepClean(Bool.pick(List<&2, Cli.Item>, c, r <> rest, rest)):
  match c:
    case True{}: k(d)
    case False{}: d

def glob_pick(b: Bool, +usage: String, +help: String,
    +attrs: List<&2, Cli.Item>, -rest: List<&2, Cli.Item>,
    ic: InfoClean(Cli.arg_info(usage, attrs)), dr: DeepClean(rest)) ->
    DeepClean(Bool.pick(List<&2, Cli.Item>, b,
      Cli.Arg{usage, help, attrs} <> rest, rest)):
  match b:
    case True{}: (ic, dr)
    case False{}: dr

def deep_globals_go(items: List<&2, Cli.Item>, +all: List<&2, Cli.Item>,
    di: DeepClean(items)) -> DeepClean(Cli.global_go(items, all)):
  match items:
    case Nil{}: Unit{}
    case Cli.Arg{+usage, +help, +attrs} <> +tail:
      (ic, dt) = di
      glob_pick(Cli.has_global(attrs), usage, help, attrs,
        Cli.global_go(tail, all), ic, deep_globals_go(tail, all, dt))
    case Cli.Sub{name, about, children} <> +tail:
      (dc, dt) = di
      deep_globals_go(tail, all, dt)
    case Cli.Version{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Alias{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Hidden{} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Example{x0, x1} <> +tail: deep_globals_go(tail, all, di)
    case Cli.After{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.SubOptional{} <> +tail: deep_globals_go(tail, all, di)
    case Cli.External{} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Exclusive{+x0} <> +tail:
      deep_rule_pick(Cli.group_global(all, x0), Cli.Exclusive{x0},
        Cli.global_go(tail, all), deep_globals_go(tail, all, di), d => d)
    case Cli.NeedOne{+x0} <> +tail:
      deep_rule_pick(Cli.group_global(all, x0), Cli.NeedOne{x0},
        Cli.global_go(tail, all), deep_globals_go(tail, all, di), d => d)
    case Cli.Id{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Required{} <> +tail: deep_globals_go(tail, all, di)
    case Cli.AttrDefault{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.AttrEnv{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Global{} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Heading{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.As{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.OneOf{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Delim{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Hyphen{} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Rest{} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Bare{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Conflicts{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Requires{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Group{x0} <> +tail: deep_globals_go(tail, all, di)
    case Cli.Builtin{} <> +tail: deep_globals_go(tail, all, di)

def deep_globals(+items: List<&2, Cli.Item>, di: DeepClean(items)) ->
    DeepClean(Cli.global_items(items)):
  deep_globals_go(items, items, di)

def SubClean(found: Maybe<&2, Cli.SubFound>) -> Type:
  match found:
    case None{}: Unit
    case Some{Cli.SubFound{name, items}}: DeepClean(items)

def alias_clean(b: Bool, -name: String, +children: List<&2, Cli.Item>,
    dc: DeepClean(children)) -> SubClean(Cli.alias_hit(b, name, children)):
  match b:
    case True{}: dc
    case False{}: Unit{}

def hit_clean(same: Bool, -name: String, +children: List<&2, Cli.Item>,
    +query: String, dc: DeepClean(children)) ->
    SubClean(Cli.sub_hit(same, name, children, query)):
  match same:
    case True{}: dc
    case False{}:
      alias_clean(Cli.has_alias(children, query, False{}), name, children, dc)

def scope_sub_step(item: Cli.Item, +tail: List<&2, Cli.Item>, +query: String,
    di: DeepClean(item <> tail),
    ih: @f: Maybe<&2, Cli.SubFound> -> SubClean(f) -> DeepClean(tail) ->
      SubClean(Cli.find_sub_go(tail, query, f))) ->
    SubClean(Cli.find_sub_go(item <> tail, query, None{})):
  match item:
    case Cli.Arg{usage, help, attrs}:
      (ic, dt) = di
      ih(None{}, Unit{}, dt)
    case Cli.Sub{+name, about, +children}:
      (dc, dt) = di
      ih(Cli.sub_hit(Cli.same_text(query, name), name, children, query),
        hit_clean(Cli.same_text(query, name), name, children, query, dc), dt)
    case Cli.Version{x0}: ih(None{}, Unit{}, di)
    case Cli.Alias{x0}: ih(None{}, Unit{}, di)
    case Cli.Hidden{}: ih(None{}, Unit{}, di)
    case Cli.Example{x0, x1}: ih(None{}, Unit{}, di)
    case Cli.After{x0}: ih(None{}, Unit{}, di)
    case Cli.SubOptional{}: ih(None{}, Unit{}, di)
    case Cli.External{}: ih(None{}, Unit{}, di)
    case Cli.Exclusive{x0}: ih(None{}, Unit{}, di)
    case Cli.NeedOne{x0}: ih(None{}, Unit{}, di)
    case Cli.Id{x0}: ih(None{}, Unit{}, di)
    case Cli.Required{}: ih(None{}, Unit{}, di)
    case Cli.AttrDefault{x0}: ih(None{}, Unit{}, di)
    case Cli.AttrEnv{x0}: ih(None{}, Unit{}, di)
    case Cli.Global{}: ih(None{}, Unit{}, di)
    case Cli.Heading{x0}: ih(None{}, Unit{}, di)
    case Cli.As{x0}: ih(None{}, Unit{}, di)
    case Cli.OneOf{x0}: ih(None{}, Unit{}, di)
    case Cli.Delim{x0}: ih(None{}, Unit{}, di)
    case Cli.Hyphen{}: ih(None{}, Unit{}, di)
    case Cli.Rest{}: ih(None{}, Unit{}, di)
    case Cli.Bare{x0}: ih(None{}, Unit{}, di)
    case Cli.Conflicts{x0}: ih(None{}, Unit{}, di)
    case Cli.Requires{x0}: ih(None{}, Unit{}, di)
    case Cli.Group{x0}: ih(None{}, Unit{}, di)
    case Cli.Builtin{}: ih(None{}, Unit{}, di)

def deep_sub_go(items: List<&2, Cli.Item>, found: Maybe<&2, Cli.SubFound>,
    +query: String, di: DeepClean(items), df: SubClean(found)) ->
    SubClean(Cli.find_sub_go(items, query, found)):
  match items:
    case Nil{}:
      match found:
        case None{}: Unit{}
        case Some{hit}: df
    case item <> +tail:
      match found:
        case Some{hit}: df
        case None{}:
          scope_sub_step(item, tail, query, di,
            f => dfc => dt => deep_sub_go(tail, f, query, dt, dfc))

def sub_items_clean(found: Maybe<&2, Cli.SubFound>, df: SubClean(found)) ->
    DeepClean(Cli.sub_items(found)):
  match found:
    case None{}: Unit{}
    case Some{Cli.SubFound{name, items}}: df

# dup_deep hands a continuation two copies of a DeepClean proof.

def default_two(-C: Type, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +value: String, +a: {Cli.kind_default_allowed(kind) == True{} : Bool},
    +b: {Cli.value_issue(kind, attrs, value) == None{} : Maybe<&2, Cli.Bad>},
    k: DefaultOk(Some{value}, kind, attrs) ->
      DefaultOk(Some{value}, kind, attrs) -> C) -> C:
  k((a, b), (a, b))

def dup_default(-C: Type, found: Maybe<&2, String>, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, ok: DefaultOk(found, kind, attrs),
    k: DefaultOk(found, kind, attrs) -> DefaultOk(found, kind, attrs) -> C) ->
    C:
  match found:
    case None{}: k(Unit{}, Unit{})
    case Some{+value}:
      (a, b) = ok
      default_two(C, kind, attrs, value, a, b, k)

def delim_two(-C: Type, -sep: Char, +kind: Cli.UsageKind,
    +e: {Cli.kind_delim_allowed(kind) == True{} : Bool},
    k: DelimOk(Some{sep}, kind) -> DelimOk(Some{sep}, kind) -> C) -> C:
  k(e, e)

def dup_delim(-C: Type, found: Maybe<&2, Char>, +kind: Cli.UsageKind,
    ok: DelimOk(found, kind),
    k: DelimOk(found, kind) -> DelimOk(found, kind) -> C) -> C:
  match found:
    case None{}: k(Unit{}, Unit{})
    case Some{sep}: delim_two(C, sep, kind, ok, k)

def choices_two(-C: Type, +values: List<&2, String>,
    +kind: Maybe<&2, Cli.ValueType>,
    +e: {Cli.choice_bad(values, kind, None{}) == None{} : Maybe<&2, Cli.Bad>},
    k: ChoicesOk(Some{values}, kind) -> ChoicesOk(Some{values}, kind) -> C) ->
    C:
  k(e, e)

def dup_choices(-C: Type, found: Maybe<&2, List<&2, String>>,
    +kind: Maybe<&2, Cli.ValueType>, ok: ChoicesOk(found, kind),
    k: ChoicesOk(found, kind) -> ChoicesOk(found, kind) -> C) -> C:
  match found:
    case None{}: k(Unit{}, Unit{})
    case Some{+values}: choices_two(C, values, kind, ok, k)

def dup_info(-C: Type, info: Cli.ArgInfo, ic: InfoClean(info),
    k: InfoClean(info) -> InfoClean(info) -> C) -> C:
  match info:
    case Cli.ArgInfo{id, usage, short, long, +kind, +attrs}:
      (okd, rest) = ic
      (okl, okc) = rest
      dup_default(C, Cli.find_default(attrs), kind, attrs, okd,
        d1 => d2 => dup_delim(C, Cli.find_delim(attrs), kind, okl,
          l1 => l2 => dup_choices(C, Cli.find_one_of(attrs), Cli.find_as(attrs),
            okc, c1 => c2 => k((d1, (l1, c1)), (d2, (l2, c2))))))

def dup_deep(-C: Type, items: List<&2, Cli.Item>, d: DeepClean(items),
    k: DeepClean(items) -> DeepClean(items) -> C) -> C:
  match items:
    case Nil{}: k(Unit{}, Unit{})
    case Cli.Arg{usage, help, attrs} <> +tail:
      (ic, dt) = d
      dup_info(C, Cli.arg_info(usage, attrs), ic,
        i1 => i2 => dup_deep(C, tail, dt, t1 => t2 => k((i1, t1), (i2, t2))))
    case Cli.Sub{name, about, +children} <> +tail:
      (dc, dt) = d
      dup_deep(C, children, dc,
        c1 => c2 => dup_deep(C, tail, dt, t1 => t2 => k((c1, t1), (c2, t2))))
    case Cli.Version{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Alias{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Hidden{} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Example{x0, x1} <> +tail: dup_deep(C, tail, d, k)
    case Cli.After{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.SubOptional{} <> +tail: dup_deep(C, tail, d, k)
    case Cli.External{} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Exclusive{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.NeedOne{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Id{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Required{} <> +tail: dup_deep(C, tail, d, k)
    case Cli.AttrDefault{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.AttrEnv{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Global{} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Heading{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.As{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.OneOf{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Delim{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Hyphen{} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Rest{} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Bare{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Conflicts{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Requires{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Group{x0} <> +tail: dup_deep(C, tail, d, k)
    case Cli.Builtin{} <> +tail: dup_deep(C, tail, d, k)

def deep_scope(path: List<&2, String>, +items: List<&2, Cli.Item>,
    +globals: List<&2, Cli.Item>, di: DeepClean(items),
    dg: DeepClean(globals)) -> DeepClean(Cli.scope_args(path, items, globals)):
  match path:
    case Nil{}: deep_append(globals, items, dg, di)
    case +name <> +tail:
      dup_deep(DeepClean(Cli.scope_args(tail,
        Cli.sub_items(Cli.find_sub(items, name)),
        List.append(&2, Cli.Item, Cli.global_items(items), globals))), items, di,
        d1 => d2 => deep_scope(tail, Cli.sub_items(Cli.find_sub(items, name)),
          List.append(&2, Cli.Item, Cli.global_items(items), globals),
          sub_items_clean(Cli.find_sub(items, name),
            deep_sub_go(items, None{}, name, d1, Unit{})),
          deep_append(Cli.global_items(items), globals,
            deep_globals(items, d2), dg)))

# P21 sample lookup: the arg an id finds has the facts.

def FoundClean(found: Maybe<&2, Cli.ArgInfo>) -> Type:
  match found:
    case None{}: Unit
    case Some{info}: InfoClean(info)

def pick_clean(b: Bool, +info: Cli.ArgInfo, ic: InfoClean(info)) ->
    FoundClean(Bool.pick(Maybe<&2, Cli.ArgInfo>, b, Some{info}, None{})):
  match b:
    case True{}: ic
    case False{}: Unit{}

def find_step(item: Cli.Item, +tail: List<&2, Cli.Item>, +id: String,
    di: DeepClean(item <> tail),
    ih: @f: Maybe<&2, Cli.ArgInfo> -> FoundClean(f) -> DeepClean(tail) ->
      FoundClean(Cli.find_arg_go(tail, id, f))) ->
    FoundClean(Cli.find_arg_go(item <> tail, id, None{})):
  match item:
    case Cli.Arg{+usage, +help, +attrs}:
      (ic, dt) = di
      ih(Cli.arg_info_found(Cli.Arg{usage, help, attrs}, id),
        pick_clean(Cli.same_text(Cli.info_id(Cli.arg_info(usage, attrs)), id),
          Cli.arg_info(usage, attrs), ic), dt)
    case Cli.Sub{name, about, children}:
      (dc, dt) = di
      ih(None{}, Unit{}, dt)
    case Cli.Version{x0}: ih(None{}, Unit{}, di)
    case Cli.Alias{x0}: ih(None{}, Unit{}, di)
    case Cli.Hidden{}: ih(None{}, Unit{}, di)
    case Cli.Example{x0, x1}: ih(None{}, Unit{}, di)
    case Cli.After{x0}: ih(None{}, Unit{}, di)
    case Cli.SubOptional{}: ih(None{}, Unit{}, di)
    case Cli.External{}: ih(None{}, Unit{}, di)
    case Cli.Exclusive{x0}: ih(None{}, Unit{}, di)
    case Cli.NeedOne{x0}: ih(None{}, Unit{}, di)
    case Cli.Id{x0}: ih(None{}, Unit{}, di)
    case Cli.Required{}: ih(None{}, Unit{}, di)
    case Cli.AttrDefault{x0}: ih(None{}, Unit{}, di)
    case Cli.AttrEnv{x0}: ih(None{}, Unit{}, di)
    case Cli.Global{}: ih(None{}, Unit{}, di)
    case Cli.Heading{x0}: ih(None{}, Unit{}, di)
    case Cli.As{x0}: ih(None{}, Unit{}, di)
    case Cli.OneOf{x0}: ih(None{}, Unit{}, di)
    case Cli.Delim{x0}: ih(None{}, Unit{}, di)
    case Cli.Hyphen{}: ih(None{}, Unit{}, di)
    case Cli.Rest{}: ih(None{}, Unit{}, di)
    case Cli.Bare{x0}: ih(None{}, Unit{}, di)
    case Cli.Conflicts{x0}: ih(None{}, Unit{}, di)
    case Cli.Requires{x0}: ih(None{}, Unit{}, di)
    case Cli.Group{x0}: ih(None{}, Unit{}, di)
    case Cli.Builtin{}: ih(None{}, Unit{}, di)

def find_clean(items: List<&2, Cli.Item>, found: Maybe<&2, Cli.ArgInfo>,
    +id: String, di: DeepClean(items), df: FoundClean(found)) ->
    FoundClean(Cli.find_arg_go(items, id, found)):
  match items:
    case Nil{}:
      match found:
        case None{}: Unit{}
        case Some{hit}: df
    case item <> +tail:
      match found:
        case Some{hit}: df
        case None{}:
          find_step(item, tail, id, di,
            f => dfc => dt => find_clean(tail, f, id, dt, dfc))

def fin_info(info: Cli.ArgInfo, +id: String, -name: String,
    -path: List<&2, String>, +want: Cli.Want, ok: InfoClean(info)) ->
    {Laws.read_at(Cli.arg_verdict(Some{info}, id, name, path, want), want,
      found_vals(Some{info})) == True{} : Bool}:
  match info:
    case Cli.ArgInfo{key, usage, short, long, +kind, +attrs}:
      (okd, rest) = ok
      (okl, okc) = rest
      core(want, kind, attrs, id, okd, okl, okc)

def fin(found: Maybe<&2, Cli.ArgInfo>, +id: String, -name: String,
    -path: List<&2, String>, +want: Cli.Want, ok: FoundClean(found)) ->
    {Laws.read_at(Cli.arg_verdict(found, id, name, path, want), want,
      found_vals(found)) == True{} : Bool}:
  match found:
    case None{}: {==}
    case Some{info}: fin_info(info, id, name, path, want, ok)

def Laws.p21_sample(c, path, id, want, e):
  match c:
    case Cli.Cmd{+name, +about, +items}:
      %sample_align(Cli.scope_args(path, items, Nil{}), id) :
        {Laws.read_at(Cli.arg_verdict(Cli.find_arg_info(Cli.scope_args(path,
          items, Nil{}), id), id, name, path, want), want, _) == True{} : Bool}
      fin(Cli.find_arg_info(Cli.scope_args(path, items, Nil{}), id), id, name,
        path, want, find_clean(Cli.scope_args(path, items, Nil{}), None{}, id,
          deep_scope(path, items, Nil{}, lint_clean(name, about, items, e),
            Unit{}), Unit{}))

# P21 fields: what any field's values satisfy (vs_ok), and that a field that
# satisfies it, and is there unless its arg may be absent, reads well once
# its verdict passes (final).

def no_bad(m: Maybe<&2, Cli.Bad>) -> Bool:
  match m:
    case None{}: True{}
    case Some{b}: False{}

def vs_ok(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +vs: List<&2, String>) -> Bool:
  match kind:
    case Cli.FlagKind{}:
      Bool.and(Laws.read_flags(vs), Laws.read_most_one(vs))
    case Cli.CountKind{}:
      Bool.and(Laws.read_counts(vs), Laws.read_most_one(vs))
    case Cli.NegatableKind{}:
      Bool.and(Laws.read_flags(vs), Laws.read_most_one(vs))
    case Cli.OptionKind{many}:
      Bool.and(no_bad(Cli.first_bad(vs, attrs)),
        Bool.or(many, Laws.read_most_one(vs)))
    case Cli.BareOptionKind{}:
      Bool.and(no_bad(Cli.first_bad(vs, attrs)), Laws.read_most_one(vs))
    case Cli.PosKind{required, many}:
      Bool.and(no_bad(Cli.first_bad(vs, attrs)),
        Bool.or(many, Laws.read_most_one(vs)))

# Empty values for a single-valued arg that is always present.
def gap(+kind: Cli.UsageKind, attrs: List<&2, Cli.Item>,
    vs: List<&2, String>) -> Bool:
  Bool.and(List.is_empty(&2, String, vs),
    Bool.and(Bool.not(Cli.kind_many(kind)), Cli.always_present(kind, attrs)))

def no_bad_none(m: Maybe<&2, Cli.Bad>, e: {no_bad(m) == True{} : Bool}) ->
    {m == None{} : Maybe<&2, Cli.Bad>}:
  match m:
    case None{}: {==}
    case Some{b}:
      Empty.absurd({Some{b} == None{} : Maybe<&2, Cli.Bad>},
        false_true_absurd(e))

def absent_none(b: Bool, -id: String, -r: String,
    e: {Cli.absent_verdict(b, id, r) == None{} : Maybe<&2, String>}) ->
    {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        why_some_absurd(String.concat(["'", id,
          "' may be absent; read it with Cli.", r, "_opt"]), e))
    case False{}: {==}

def and_true_false(a: Bool, e: {Bool.and(a, True{}) == False{} : Bool}) ->
    {a == False{} : Bool}:
  match a:
    case True{}: e
    case False{}: {==}

# An always-present arg's values, which gap says are not empty, hold one
# value once they hold at most one.
def one_present(ap: Bool, +vs: List<&2, String>,
    ex: {Bool.not(ap) == False{} : Bool},
    ep: {Bool.and(List.is_empty(&2, String, vs), ap) == False{} : Bool},
    em: {Laws.read_most_one(vs) == True{} : Bool}) ->
    {Laws.read_one(vs) == True{} : Bool}:
  match ap:
    case True{}:
      match vs:
        case Nil{}:
          Empty.absurd({Laws.read_one(Nil{}) == True{} : Bool},
            true_false_absurd(ep))
        case v <> t: em
    case False{}:
      Empty.absurd({Laws.read_one(vs) == True{} : Bool},
        true_false_absurd(ex))

def flag_final(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>, +id: String,
    +vs: List<&2, String>, ev: {vs_ok(kind, attrs, vs) == True{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(Cli.WFlag{}, id, kind, attrs), Cli.WFlag{},
      vs) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}: ev
    case Cli.CountKind{}: {==}
    case Cli.NegatableKind{}: ev
    case Cli.OptionKind{many}: {==}
    case Cli.BareOptionKind{}: {==}
    case Cli.PosKind{required, many}: {==}

def count_final(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>, +id: String,
    +vs: List<&2, String>, ev: {vs_ok(kind, attrs, vs) == True{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(Cli.WCount{}, id, kind, attrs),
      Cli.WCount{}, vs) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}: {==}
    case Cli.CountKind{}: ev
    case Cli.NegatableKind{}: {==}
    case Cli.OptionKind{many}: {==}
    case Cli.BareOptionKind{}: {==}
    case Cli.PosKind{required, many}: {==}

# want_verdict for a value or choose reader, given its kind check, absence
# check and (for choose) keys check pass.
def at_two(a: Bool, x: Maybe<&2, String>, -id: String, -kind: Cli.UsageKind,
    -attrs: List<&2, Cli.Item>, -w: Cli.Want, -vals: List<&2, String>,
    g: {a == True{} : Bool} -> {x == None{} : Maybe<&2, String>} ->
      {Laws.read_good(w, vals) == True{} : Bool}) ->
    {Laws.read_at(Maybe.or(&2, String, Cli.kind_verdict(a, id, kind, attrs),
      x), w, vals) == True{} : Bool}:
  match a:
    case True{}:
      match x:
        case None{}: g({==})({==})
        case Some{m}: {==}
    case False{}: {==}

def xy_none(x: Maybe<&2, String>, y: Maybe<&2, String>, -w: Cli.Want,
    -vals: List<&2, String>,
    g: {x == None{} : Maybe<&2, String>} -> {y == None{} : Maybe<&2, String>} ->
      {Laws.read_good(w, vals) == True{} : Bool}) ->
    {Laws.read_at(Maybe.or(&2, String, x, y), w, vals) == True{} : Bool}:
  match x y:
    case Some{m} _: {==}
    case None{} Some{m}: {==}
    case None{} None{}: g({==})({==})

def at_three(a: Bool, x: Maybe<&2, String>, y: Maybe<&2, String>,
    -id: String, -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>,
    -w: Cli.Want, -vals: List<&2, String>,
    g: {a == True{} : Bool} -> {x == None{} : Maybe<&2, String>} ->
      {y == None{} : Maybe<&2, String>} ->
      {Laws.read_good(w, vals) == True{} : Bool}) ->
    {Laws.read_at(Maybe.or(&2, String, Cli.kind_verdict(a, id, kind, attrs),
      Maybe.or(&2, String, x, y)), w, vals) == True{} : Bool}:
  match a:
    case True{}: xy_none(x, y, w, vals, g({==}))
    case False{}: {==}

def all_stem(+stem: String, +attrs: List<&2, Cli.Item>, +vs: List<&2, String>,
    es: {String.eq(stem, Cli.type_stem(Cli.find_as(attrs))) == True{} : Bool},
    nb: {Cli.first_bad(vs, attrs) == None{} : Maybe<&2, Cli.Bad>}) ->
    {Laws.read_all(vs, stem) == True{} : Bool}:
  %Equal.sym(String, stem, Cli.type_stem(Cli.find_as(attrs)),
    eq_reflect(stem, Cli.type_stem(Cli.find_as(attrs)), es)) :
    {Laws.read_all(vs, _) == True{} : Bool}
  first_bad_ok(vs, attrs, nb)

# A valued arg's values, m saying whether it takes many, under form.
def form_good(form: Cli.Form, m: Bool, ap: Bool, +vs: List<&2, String>,
    em: {Bool.or(m, Laws.read_most_one(vs)) == True{} : Bool},
    ep: {Bool.and(List.is_empty(&2, String, vs), Bool.and(Bool.not(m), ap))
      == False{} : Bool},
    ef: {Cli.form_fits(form, m) == True{} : Bool},
    ex: {Bool.and(Cli.form_one(form), Bool.and(Bool.not(m), Bool.not(ap)))
      == False{} : Bool}) ->
    {Laws.read_form(form, vs) == True{} : Bool}:
  match form m:
    case Cli.ReadOne{} True{}:
      Empty.absurd({Laws.read_one(vs) == True{} : Bool},
        false_true_absurd(ef))
    case Cli.ReadOne{} False{}: one_present(ap, vs, ex, ep, em)
    case Cli.ReadOpt{} True{}:
      Empty.absurd({Laws.read_most_one(vs) == True{} : Bool},
        false_true_absurd(ef))
    case Cli.ReadOpt{} False{}: em
    case Cli.ReadMany{} _: {==}

def valued_good(+m: Bool, ap: Bool, +stem: String, +form: Cli.Form,
    +attrs: List<&2, Cli.Item>, +vs: List<&2, String>,
    +ev: {Bool.and(no_bad(Cli.first_bad(vs, attrs)),
      Bool.or(m, Laws.read_most_one(vs))) == True{} : Bool},
    ep: {Bool.and(List.is_empty(&2, String, vs), Bool.and(Bool.not(m), ap))
      == False{} : Bool},
    +ea: {Bool.and(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
      Cli.form_fits(form, m)) == True{} : Bool},
    ex: {Bool.and(Cli.form_one(form), Bool.and(Bool.not(m), Bool.not(ap)))
      == False{} : Bool}) ->
    {Laws.read_good(Cli.WValue{stem, form}, vs) == True{} : Bool}:
  and_true(Laws.read_all(vs, stem), Laws.read_form(form, vs),
    all_stem(stem, attrs, vs,
      and_left(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
        Cli.form_fits(form, m), ea),
      no_bad_none(Cli.first_bad(vs, attrs),
        and_left(no_bad(Cli.first_bad(vs, attrs)),
          Bool.or(m, Laws.read_most_one(vs)), ev))),
    form_good(form, m, ap, vs,
      and_right(no_bad(Cli.first_bad(vs, attrs)),
        Bool.or(m, Laws.read_most_one(vs)), ev),
      ep,
      and_right(String.eq(stem, Cli.type_stem(Cli.find_as(attrs))),
        Cli.form_fits(form, m), ea),
      ex))

def value_kind(kind: Cli.UsageKind, +stem: String, +form: Cli.Form,
    +attrs: List<&2, Cli.Item>, +id: String, +vs: List<&2, String>,
    ev: {vs_ok(kind, attrs, vs) == True{} : Bool},
    ep: {gap(kind, attrs, vs) == False{} : Bool},
    ea: {Cli.value_fits(stem, form, kind, attrs) == True{} : Bool},
    ex: {Cli.absent_verdict(Bool.and(Cli.form_one(form),
      Cli.may_absent(kind, attrs)), id, stem) == None{} : Maybe<&2, String>}) ->
    {Laws.read_good(Cli.WValue{stem, form}, vs) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}:
      Empty.absurd({Laws.read_good(Cli.WValue{stem, form}, vs) == True{}
        : Bool}, false_true_absurd(ea))
    case Cli.CountKind{}:
      Empty.absurd({Laws.read_good(Cli.WValue{stem, form}, vs) == True{}
        : Bool}, false_true_absurd(ea))
    case Cli.NegatableKind{}:
      Empty.absurd({Laws.read_good(Cli.WValue{stem, form}, vs) == True{}
        : Bool}, false_true_absurd(ea))
    case Cli.OptionKind{+many}:
      valued_good(many, Cli.always_present(Cli.OptionKind{many}, attrs), stem,
        form, attrs, vs, ev, ep, ea,
        absent_none(Bool.and(Cli.form_one(form),
          Cli.may_absent(Cli.OptionKind{many}, attrs)), id, stem, ex))
    case Cli.BareOptionKind{}:
      valued_good(False{}, Cli.always_present(Cli.BareOptionKind{}, attrs),
        stem, form, attrs, vs, ev, ep, ea,
        absent_none(Bool.and(Cli.form_one(form),
          Cli.may_absent(Cli.BareOptionKind{}, attrs)), id, stem, ex))
    case Cli.PosKind{+required, +many}:
      valued_good(many, Cli.always_present(Cli.PosKind{required, many},
          attrs), stem, form, attrs, vs, ev, ep, ea,
        absent_none(Bool.and(Cli.form_one(form),
          Cli.may_absent(Cli.PosKind{required, many}, attrs)), id, stem, ex))

def value_final(+kind: Cli.UsageKind, +stem: String, +form: Cli.Form,
    +attrs: List<&2, Cli.Item>, +id: String, +vs: List<&2, String>,
    ev: {vs_ok(kind, attrs, vs) == True{} : Bool},
    ep: {gap(kind, attrs, vs) == False{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(Cli.WValue{stem, form}, id, kind, attrs),
      Cli.WValue{stem, form}, vs) == True{} : Bool}:
  at_two(Cli.value_fits(stem, form, kind, attrs),
    Cli.absent_verdict(Bool.and(Cli.form_one(form),
      Cli.may_absent(kind, attrs)), id, stem), id, kind, attrs,
    Cli.WValue{stem, form}, vs,
    ea => ex => value_kind(kind, stem, form, attrs, id, vs, ev, ep, ea, ex))

# Each value first_bad passes is among choose's keys.
def keys_all(vs: List<&2, String>, +keys: List<&2, String>,
    +attrs: List<&2, Cli.Item>, +id: String,
    nb: {Cli.first_bad(vs, attrs) == None{} : Maybe<&2, Cli.Bad>},
    +es: {Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs))
      == True{} : Bool},
    +ey: {Cli.keys_verdict(Cli.find_one_of(attrs), keys, id) == None{}
      : Maybe<&2, String>}) ->
    {Laws.read_keys(vs, keys) == True{} : Bool}:
  match vs:
    case Nil{}: {==}
    case +head <> +tail:
      pair_elim({Cli.bad_value(Cli.value_reason(attrs, head), head) == None{}
        : Maybe<&2, Cli.Bad>},
        {Cli.first_bad(tail, attrs) == None{} : Maybe<&2, Cli.Bad>},
        {Laws.read_keys(head <> tail, keys) == True{} : Bool},
        or_bad_none(Cli.bad_value(Cli.value_reason(attrs, head), head),
          Cli.first_bad(tail, attrs), nb),
        eh => et => and_true(
          List.contains(~String, ~String.eq, keys, head),
          Laws.read_keys(tail, keys),
          choice_in(Cli.find_one_of(attrs), keys, id, head, es,
            Pair.snd({Cli.reason_from_type(Cli.find_as(attrs), head) == None{}
              : Maybe<&2, String>},
              {Cli.choice_reason(Cli.find_one_of(attrs), head) == None{}
                : Maybe<&2, String>},
              first_reason_none(Cli.reason_from_type(Cli.find_as(attrs), head),
                Cli.choice_reason(Cli.find_one_of(attrs), head),
                bad_value_none(Cli.value_reason(attrs, head), head, eh))),
            ey),
          keys_all(tail, keys, attrs, id, et, es, ey)))

def choose_read(opt: Bool, ap: Bool, +vs: List<&2, String>,
    em: {Laws.read_most_one(vs) == True{} : Bool},
    ep: {Bool.and(List.is_empty(&2, String, vs), ap) == False{} : Bool},
    ex: {Bool.and(Bool.not(opt), Bool.not(ap)) == False{} : Bool}) ->
    {Laws.read_choose(opt, vs) == True{} : Bool}:
  match opt:
    case True{}: em
    case False{}: one_present(ap, vs, ex, ep, em)

def chosen_good(ap: Bool, +opt: Bool, +keys: List<&2, String>,
    +attrs: List<&2, Cli.Item>, +id: String, +vs: List<&2, String>,
    +ev: {Bool.and(no_bad(Cli.first_bad(vs, attrs)), Laws.read_most_one(vs))
      == True{} : Bool},
    ep: {Bool.and(List.is_empty(&2, String, vs), ap) == False{} : Bool},
    es: {Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs))
      == True{} : Bool},
    ex: {Bool.and(Bool.not(opt), Bool.not(ap)) == False{} : Bool},
    ey: {Cli.keys_verdict(Cli.find_one_of(attrs), keys, id) == None{}
      : Maybe<&2, String>}) ->
    {Laws.read_good(Cli.WChoose{opt, keys}, vs) == True{} : Bool}:
  and_true(Laws.read_choose(opt, vs), Laws.read_keys(vs, keys),
    choose_read(opt, ap, vs,
      and_right(no_bad(Cli.first_bad(vs, attrs)), Laws.read_most_one(vs), ev),
      ep, ex),
    keys_all(vs, keys, attrs, id,
      no_bad_none(Cli.first_bad(vs, attrs),
        and_left(no_bad(Cli.first_bad(vs, attrs)), Laws.read_most_one(vs),
          ev)), es, ey))

def single_many(many: Bool, e: {Bool.not(many) == True{} : Bool}) ->
    {many == False{} : Bool}:
  match many:
    case True{}: Equal.sym(Bool, False{}, True{}, e)
    case False{}: {==}

def choose_many(many: Bool, +opt: Bool, +keys: List<&2, String>,
    +attrs: List<&2, Cli.Item>, +id: String, +vs: List<&2, String>, ap: Bool,
    +ev: {Bool.and(no_bad(Cli.first_bad(vs, attrs)),
      Bool.or(many, Laws.read_most_one(vs))) == True{} : Bool},
    ep: {Bool.and(List.is_empty(&2, String, vs), Bool.and(Bool.not(many), ap))
      == False{} : Bool},
    ea: {Bool.and(Bool.not(many), Maybe.is_some(&2, List<&2, String>,
      Cli.find_one_of(attrs))) == True{} : Bool},
    ex: {Bool.and(Bool.not(opt), Bool.and(Bool.not(many), Bool.not(ap)))
      == False{} : Bool},
    ey: {Cli.keys_verdict(Cli.find_one_of(attrs), keys, id) == None{}
      : Maybe<&2, String>}) ->
    {Laws.read_good(Cli.WChoose{opt, keys}, vs) == True{} : Bool}:
  match many:
    case True{}:
      Empty.absurd({Laws.read_good(Cli.WChoose{opt, keys}, vs) == True{}
        : Bool}, false_true_absurd(ea))
    case False{}: chosen_good(ap, opt, keys, attrs, id, vs, ev, ep, ea, ex, ey)

def choose_kind(kind: Cli.UsageKind, +opt: Bool, +keys: List<&2, String>,
    +attrs: List<&2, Cli.Item>, +id: String, +vs: List<&2, String>,
    ev: {vs_ok(kind, attrs, vs) == True{} : Bool},
    ep: {gap(kind, attrs, vs) == False{} : Bool},
    ea: {Cli.choose_fits(kind, attrs) == True{} : Bool},
    ex: {Cli.absent_verdict(Bool.and(Bool.not(opt),
      Cli.may_absent(kind, attrs)), id, "choose") == None{}
      : Maybe<&2, String>},
    ey: {Cli.keys_verdict(Cli.find_one_of(attrs), keys, id) == None{}
      : Maybe<&2, String>}) ->
    {Laws.read_good(Cli.WChoose{opt, keys}, vs) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}:
      Empty.absurd({Laws.read_good(Cli.WChoose{opt, keys}, vs) == True{}
        : Bool}, false_true_absurd(ea))
    case Cli.CountKind{}:
      Empty.absurd({Laws.read_good(Cli.WChoose{opt, keys}, vs) == True{}
        : Bool}, false_true_absurd(ea))
    case Cli.NegatableKind{}:
      Empty.absurd({Laws.read_good(Cli.WChoose{opt, keys}, vs) == True{}
        : Bool}, false_true_absurd(ea))
    case Cli.OptionKind{+many}:
      choose_many(many, opt, keys, attrs, id, vs,
        Cli.always_present(Cli.OptionKind{many}, attrs), ev, ep, ea,
        absent_none(Bool.and(Bool.not(opt),
          Cli.may_absent(Cli.OptionKind{many}, attrs)), id, "choose", ex), ey)
    case Cli.BareOptionKind{}:
      chosen_good(Cli.always_present(Cli.BareOptionKind{}, attrs), opt, keys,
        attrs, id, vs, ev, ep, ea,
        absent_none(Bool.and(Bool.not(opt),
          Cli.may_absent(Cli.BareOptionKind{}, attrs)), id, "choose", ex), ey)
    case Cli.PosKind{+required, +many}:
      choose_many(many, opt, keys, attrs, id, vs,
        Cli.always_present(Cli.PosKind{required, many}, attrs), ev, ep, ea,
        absent_none(Bool.and(Bool.not(opt),
          Cli.may_absent(Cli.PosKind{required, many}, attrs)), id, "choose",
          ex), ey)

def choose_final(+kind: Cli.UsageKind, +opt: Bool, +keys: List<&2, String>,
    +attrs: List<&2, Cli.Item>, +id: String, +vs: List<&2, String>,
    ev: {vs_ok(kind, attrs, vs) == True{} : Bool},
    ep: {gap(kind, attrs, vs) == False{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(Cli.WChoose{opt, keys}, id, kind, attrs),
      Cli.WChoose{opt, keys}, vs) == True{} : Bool}:
  at_three(Cli.choose_fits(kind, attrs),
    Cli.absent_verdict(Bool.and(Bool.not(opt), Cli.may_absent(kind, attrs)),
      id, "choose"),
    Cli.keys_verdict(Cli.find_one_of(attrs), keys, id), id, kind, attrs,
    Cli.WChoose{opt, keys}, vs,
    ea => ex => ey => choose_kind(kind, opt, keys, attrs, id, vs, ev, ep, ea,
      ex, ey))

def final(want: Cli.Want, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +id: String, +vs: List<&2, String>,
    ev: {vs_ok(kind, attrs, vs) == True{} : Bool},
    ep: {gap(kind, attrs, vs) == False{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(want, id, kind, attrs), want, vs)
      == True{} : Bool}:
  match want:
    case Cli.WFlag{}: flag_final(kind, attrs, id, vs, ev)
    case Cli.WCount{}: count_final(kind, attrs, id, vs, ev)
    case Cli.WValue{stem, form}: value_final(kind, stem, form, attrs, id, vs, ev, ep)
    case Cli.WAny{}: {==}
    case Cli.WChoose{opt, keys}: choose_final(kind, opt, keys, attrs, id, vs, ev, ep)

# P21 field values: what env, a default and the argv give an arg satisfy
# (fgood), which gap and final then read.

def fgood(+kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +vs: List<&2, String>) -> Bool:
  Bool.and(vs_ok(kind, attrs, vs),
    Bool.or(Cli.kind_many(kind), Bool.not(List.is_empty(&2, String, vs))))

def gap_off(em: Bool, m: Bool, -ap: Bool,
    e: {Bool.or(m, Bool.not(em)) == True{} : Bool}) ->
    {Bool.and(em, Bool.and(Bool.not(m), ap)) == False{} : Bool}:
  match em:
    case True{}:
      match m:
        case True{}: {==}
        case False{}:
          Empty.absurd({Bool.and(True{}, Bool.and(True{}, ap)) == False{}
            : Bool}, false_true_absurd(e))
    case False{}: {==}

def fgood_ok(+kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +vs: List<&2, String>, e: {fgood(kind, attrs, vs) == True{} : Bool}) ->
    {vs_ok(kind, attrs, vs) == True{} : Bool}:
  and_left(vs_ok(kind, attrs, vs),
    Bool.or(Cli.kind_many(kind), Bool.not(List.is_empty(&2, String, vs))), e)

def fgood_gap(+kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +vs: List<&2, String>, e: {fgood(kind, attrs, vs) == True{} : Bool}) ->
    {gap(kind, attrs, vs) == False{} : Bool}:
  gap_off(List.is_empty(&2, String, vs), Cli.kind_many(kind),
    Cli.always_present(kind, attrs),
    and_right(vs_ok(kind, attrs, vs),
      Bool.or(Cli.kind_many(kind), Bool.not(List.is_empty(&2, String, vs))),
      e))

def nb_of(m: Maybe<&2, Cli.Bad>, e: {m == None{} : Maybe<&2, Cli.Bad>}) ->
    {no_bad(m) == True{} : Bool}:
  match m:
    case None{}: {==}
    case Some{b}:
      Empty.absurd({no_bad(Some{b}) == True{} : Bool}, bad_some_absurd(b, e))

def or_none2(m: Maybe<&2, Cli.Bad>, n: Maybe<&2, Cli.Bad>,
    em: {m == None{} : Maybe<&2, Cli.Bad>},
    en: {n == None{} : Maybe<&2, Cli.Bad>}) ->
    {Maybe.or(&2, Cli.Bad, m, n) == None{} : Maybe<&2, Cli.Bad>}:
  match m:
    case None{}: en
    case Some{b}:
      Empty.absurd({Maybe.or(&2, Cli.Bad, Some{b}, n) == None{}
        : Maybe<&2, Cli.Bad>}, bad_some_absurd(b, em))

# first_bad finds nothing in xs ++ ys when it finds nothing in either.
def fb_app(xs: List<&2, String>, +ys: List<&2, String>,
    +attrs: List<&2, Cli.Item>,
    ex: {Cli.first_bad(xs, attrs) == None{} : Maybe<&2, Cli.Bad>},
    ey: {Cli.first_bad(ys, attrs) == None{} : Maybe<&2, Cli.Bad>}) ->
    {Cli.first_bad(List.append(&2, String, xs, ys), attrs) == None{}
      : Maybe<&2, Cli.Bad>}:
  match xs:
    case Nil{}: ey
    case +head <> +tail:
      pair_elim({Cli.bad_value(Cli.value_reason(attrs, head), head) == None{}
        : Maybe<&2, Cli.Bad>},
        {Cli.first_bad(tail, attrs) == None{} : Maybe<&2, Cli.Bad>},
        {Cli.first_bad(List.append(&2, String, head <> tail, ys), attrs)
          == None{} : Maybe<&2, Cli.Bad>},
        or_bad_none(Cli.bad_value(Cli.value_reason(attrs, head), head),
          Cli.first_bad(tail, attrs), ex),
        eh => et => or_none2(Cli.bad_value(Cli.value_reason(attrs, head), head),
          Cli.first_bad(List.append(&2, String, tail, ys), attrs), eh,
          fb_app(tail, ys, attrs, et, ey)))

def fb_one(+attrs: List<&2, Cli.Item>, +v: String,
    e: {Cli.bad_value(Cli.value_reason(attrs, v), v) == None{}
      : Maybe<&2, Cli.Bad>}) ->
    {Cli.first_bad([v], attrs) == None{} : Maybe<&2, Cli.Bad>}:
  or_none2(Cli.bad_value(Cli.value_reason(attrs, v), v), None{}, e, {==})

def fb_nil(xs: List<&2, String>, +attrs: List<&2, Cli.Item>,
    e: {Cli.first_bad(xs, attrs) == None{} : Maybe<&2, Cli.Bad>}) ->
    {Cli.first_bad(List.append(&2, String, xs, Nil{}), attrs) == None{}
      : Maybe<&2, Cli.Bad>}:
  fb_app(xs, Nil{}, attrs, e, {==})

# A flag's text, from env or the argv, is "true" or "false".
def flag_env(+attrs: List<&2, Cli.Item>, b: Bool) ->
    {fgood(Cli.FlagKind{}, attrs, [Cli.bool_text(b)]) == True{} : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def neg_env(+attrs: List<&2, Cli.Item>, b: Bool) ->
    {fgood(Cli.NegatableKind{}, attrs, [Cli.bool_text(b)]) == True{} : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def nat_digits(+v: String, +e: {Cli.valid_nat(v) == True{} : Bool}) ->
    {Bool.and(Bool.not(String.is_empty(v)), Cli.decimal_digits(v)) == True{}
      : Bool}:
  and_true(Bool.not(String.is_empty(v)), Cli.decimal_digits(v),
    and_left(Bool.not(String.is_empty(v)), Bool.and(Cli.decimal_digits(v),
      Nat.read.fits(Nat.read.trim(v))), e),
    and_left(Cli.decimal_digits(v), Nat.read.fits(Nat.read.trim(v)),
      and_right(Bool.not(String.is_empty(v)), Bool.and(Cli.decimal_digits(v),
        Nat.read.fits(Nat.read.trim(v))), e)))

def count_one(+attrs: List<&2, Cli.Item>, +v: String,
    e: {Bool.and(Bool.not(String.is_empty(v)), Cli.decimal_digits(v))
      == True{} : Bool}) ->
    {fgood(Cli.CountKind{}, attrs, [v]) == True{} : Bool}:
  and_true(vs_ok(Cli.CountKind{}, attrs, [v]), True{},
    and_true(Laws.read_counts([v]), True{},
      and_true(Bool.and(Bool.not(String.is_empty(v)), Cli.decimal_digits(v)),
        True{}, e, {==}), {==}), {==})

def count_env(+attrs: List<&2, Cli.Item>, +v: String,
    iss: {Cli.value_issue(Cli.CountKind{}, attrs, v) == None{}
      : Maybe<&2, Cli.Bad>}) ->
    {fgood(Cli.CountKind{}, attrs, [v]) == True{} : Bool}:
  count_one(attrs, v, nat_digits(v,
    pick_none_true(Cli.valid_nat(v),
      "expected a whole number from 0 to 281474976710655",
      bad_value_none(Cli.type_reason(Cli.TNat{}, v), v, iss))))

# A many-valued kind's split, or a lone value.
def many_good(found: Maybe<&2, Char>, +many: Bool, +attrs: List<&2, Cli.Item>,
    +v: String,
    ev: {Cli.split_bad(found, attrs, v) == None{} : Maybe<&2, Cli.Bad>},
    okl: DelimMany(found, many)) ->
    {Bool.and(Bool.and(no_bad(Cli.first_bad(Cli.apply_delim(found, [v]),
        attrs)), Bool.or(many, Laws.read_most_one(Cli.apply_delim(found, [v])))),
      Bool.or(many, Bool.not(List.is_empty(&2, String,
        Cli.apply_delim(found, [v]))))) == True{} : Bool}:
  match found:
    case None{}:
      and_true(Bool.and(no_bad(Cli.first_bad([v], attrs)),
        Bool.or(many, True{})), Bool.or(many, True{}),
        and_true(no_bad(Cli.first_bad([v], attrs)), Bool.or(many, True{}),
          nb_of(Cli.first_bad([v], attrs), fb_one(attrs, v, ev)),
          or_true_right(many)), or_true_right(many))
    case Some{+sep}:
      match many:
        case True{}:
          and_true(Bool.and(no_bad(Cli.first_bad(List.append(&2, String,
            String.split(v, sep), Nil{}), attrs)), True{}), True{},
            and_true(no_bad(Cli.first_bad(List.append(&2, String,
              String.split(v, sep), Nil{}), attrs)), True{},
              nb_of(Cli.first_bad(List.append(&2, String,
                String.split(v, sep), Nil{}), attrs),
                fb_nil(String.split(v, sep), attrs, ev)), {==}), {==})
        case False{}:
          Empty.absurd({Bool.and(Bool.and(no_bad(Cli.first_bad(
            Cli.apply_delim(Some{sep}, [v]), attrs)), Bool.or(False{},
            Laws.read_most_one(Cli.apply_delim(Some{sep}, [v])))),
            Bool.or(False{}, Bool.not(List.is_empty(&2, String,
              Cli.apply_delim(Some{sep}, [v]))))) == True{} : Bool},
            false_true_absurd(okl))

def bare_good(found: Maybe<&2, Char>, +attrs: List<&2, Cli.Item>,
    +v: String,
    ev: {Cli.split_bad(found, attrs, v) == None{} : Maybe<&2, Cli.Bad>},
    okl: DelimOk(found, Cli.BareOptionKind{})) ->
    {fgood(Cli.BareOptionKind{}, attrs, Cli.apply_delim(found, [v]))
      == True{} : Bool}:
  match found:
    case None{}:
      and_true(Bool.and(no_bad(Cli.first_bad([v], attrs)), True{}), True{},
        and_true(no_bad(Cli.first_bad([v], attrs)), True{},
          nb_of(Cli.first_bad([v], attrs), fb_one(attrs, v, ev)), {==}),
        {==})
    case Some{sep}:
      Empty.absurd({fgood(Cli.BareOptionKind{}, attrs,
        Cli.apply_delim(Some{sep}, [v])) == True{} : Bool},
        false_true_absurd(okl))

# A value env or a default gives, once value_issue passes it.
def env_good(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>, +v: String,
    iss: {Cli.value_issue(kind, attrs, v) == None{} : Maybe<&2, Cli.Bad>},
    okl: DelimOk(Cli.find_delim(attrs), kind)) ->
    {fgood(kind, attrs, Cli.env_values(kind, attrs, v)) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}: flag_env(attrs, Cli.env_bool_true(v))
    case Cli.CountKind{}: count_env(attrs, v, iss)
    case Cli.NegatableKind{}: neg_env(attrs, Cli.env_bool_true(v))
    case Cli.OptionKind{+many}:
      many_good(Cli.find_delim(attrs), many, attrs, v, iss,
        delim_many(Cli.find_delim(attrs), Cli.OptionKind{many}, okl))
    case Cli.BareOptionKind{}:
      bare_good(Cli.find_delim(attrs), attrs, v, iss, okl)
    case Cli.PosKind{required, +many}:
      many_good(Cli.find_delim(attrs), many, attrs, v, iss,
        delim_many(Cli.find_delim(attrs), Cli.PosKind{required, many}, okl))

# P21 counts: Nat.show writes only decimal digits, at least one, since
# divmod.go's remainder stays at most 9 while it and m add up to 9.

def digit_ok(r: Nat) -> Bool:
  U32.is_lt(U32.sub(U32.from_nat(Nat.add(48n, r)), 48), 10)

def npred(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  %e : {a == npred(_) : Nat}
  {==}

def nat_nz(n: Nat) -> Data:
  match n:
    case 0n: Empty
    case 1n+p: Unit

def succ_zero_absurd(-a: Nat, e: {1n+a == 0n : Nat}) -> Empty:
  %e : nat_nz(_)
  Unit{}

def dig0(r: Nat, -m: Nat, e: {Nat.add(r, m) == 0n : Nat}) ->
    {digit_ok(Nat.add(9n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p:
      Empty.absurd({digit_ok(Nat.add(9n, 1n+p)) == True{} : Bool},
        succ_zero_absurd(Nat.add(p, m), e))

def dig1(r: Nat, -m: Nat, e: {Nat.add(r, m) == 1n : Nat}) ->
    {digit_ok(Nat.add(8n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig0(p, m, succ_inj(Nat.add(p, m), 0n, e))

def dig2(r: Nat, -m: Nat, e: {Nat.add(r, m) == 2n : Nat}) ->
    {digit_ok(Nat.add(7n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig1(p, m, succ_inj(Nat.add(p, m), 1n, e))

def dig3(r: Nat, -m: Nat, e: {Nat.add(r, m) == 3n : Nat}) ->
    {digit_ok(Nat.add(6n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig2(p, m, succ_inj(Nat.add(p, m), 2n, e))

def dig4(r: Nat, -m: Nat, e: {Nat.add(r, m) == 4n : Nat}) ->
    {digit_ok(Nat.add(5n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig3(p, m, succ_inj(Nat.add(p, m), 3n, e))

def dig5(r: Nat, -m: Nat, e: {Nat.add(r, m) == 5n : Nat}) ->
    {digit_ok(Nat.add(4n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig4(p, m, succ_inj(Nat.add(p, m), 4n, e))

def dig6(r: Nat, -m: Nat, e: {Nat.add(r, m) == 6n : Nat}) ->
    {digit_ok(Nat.add(3n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig5(p, m, succ_inj(Nat.add(p, m), 5n, e))

def dig7(r: Nat, -m: Nat, e: {Nat.add(r, m) == 7n : Nat}) ->
    {digit_ok(Nat.add(2n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig6(p, m, succ_inj(Nat.add(p, m), 6n, e))

def dig8(r: Nat, -m: Nat, e: {Nat.add(r, m) == 8n : Nat}) ->
    {digit_ok(Nat.add(1n, r)) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig7(p, m, succ_inj(Nat.add(p, m), 7n, e))

def dig9(r: Nat, -m: Nat, e: {Nat.add(r, m) == 9n : Nat}) ->
    {digit_ok(r) == True{} : Bool}:
  match r:
    case 0n: {==}
    case 1n+p: dig8(p, m, succ_inj(Nat.add(p, m), 8n, e))

def DmOk(qr: Nat & Nat) -> Type:
  match qr:
    case (q, r): {digit_ok(r) == True{} : Bool}

def dm_ok(n: Nat, m: Nat, -d: Nat, +r: Nat,
    e: {Nat.add(r, m) == 9n : Nat}) -> DmOk(Nat.divmod.go(n, m, d, r)):
  match n:
    case 0n: dig9(r, m, e)
    case 1n+np:
      match m:
        case 0n:
          dm_ok(np, r, 1n+d, 0n, Equal.trans(Nat, r, Nat.add(r, 0n), 9n,
            Equal.sym(Nat, Nat.add(r, 0n), r, add_zero_right(r)), e))
        case 1n+(+mp):
          dm_ok(np, mp, d, 1n+r, Equal.trans(Nat, 1n+Nat.add(r, mp),
            Nat.add(r, 1n+mp), 9n, Equal.sym(Nat, Nat.add(r, 1n+mp),
              1n+Nat.add(r, mp), add_succ_right(r, mp)), e))

# decimal_digits' test of a char.
def DigC(d: Char) -> Type:
  match d:
    case Chr{x}: {U32.is_lt(U32.sub(x, 48), 10) == True{} : Bool}

def DigOk(dq: Char & Nat) -> Type:
  match dq:
    case (d, q): DigC(d)

def put_dig(qr: Nat & Nat, ok: DmOk(qr)) -> DigOk(Nat.show.put(qr)):
  match qr:
    case (q, r): ok

def put_ok(+n: Nat) -> DigOk(Nat.show.put(Nat.divmod(n, 10n))):
  put_dig(Nat.divmod(n, 10n), dm_ok(n, 9n, 0n, 0n, {==}))

def cnt_ok(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), Cli.decimal_digits(s))

def fin_ok(-g: Nat, +acc: String, dq: Char & Nat,
    ea: {Cli.decimal_digits(acc) == True{} : Bool}, ed: DigOk(dq),
    ih: @n2: Nat -> @acc2: String -> {cnt_ok(acc2) == True{} : Bool} ->
      {cnt_ok(Nat.show.go(g, n2, acc2)) == True{} : Bool}) ->
    {cnt_ok(Nat.show.fin(g, acc, dq)) == True{} : Bool}:
  match dq:
    case (d, q):
      match d:
        case Chr{+x}:
          match q:
            case 0n:
              and_true(U32.is_lt(U32.sub(x, 48), 10), Cli.decimal_digits(acc),
                ed, ea)
            case 1n+p:
              ih(1n+p, SCon{Chr{x}, acc},
                and_true(U32.is_lt(U32.sub(x, 48), 10),
                  Cli.decimal_digits(acc), ed, ea))

def cnt_digits(+s: String, e: {cnt_ok(s) == True{} : Bool}) ->
    {Cli.decimal_digits(s) == True{} : Bool}:
  and_right(Bool.not(String.is_empty(s)), Cli.decimal_digits(s), e)

def show_go_ok(f: Nat, +n: Nat, +acc: String,
    ea: {cnt_ok(acc) == True{} : Bool}) ->
    {cnt_ok(Nat.show.go(f, n, acc)) == True{} : Bool}:
  match f:
    case 0n: ea
    case 1n+g:
      fin_ok(g, acc, Nat.show.put(Nat.divmod(n, 10n)), cnt_digits(acc, ea),
        put_ok(n), n2 => acc2 => e2 => show_go_ok(g, n2, acc2, e2))

def show_ok(+n: Nat) -> {cnt_ok(Nat.show(n)) == True{} : Bool}:
  fin_ok(n, SNil{}, Nat.show.put(Nat.divmod(n, 10n)), {==}, put_ok(n),
    n2 => acc2 => e2 => show_go_ok(n, n2, acc2, e2))

# P21 argv: what gather keeps for an arg once each of its hits is valid for
# it (ev_ok), and the field resolve builds from that.

def allv(vs: List<&2, String>, +found: Maybe<&2, Char>,
    +attrs: List<&2, Cli.Item>) -> Bool:
  match vs:
    case Nil{}: True{}
    case v <> t:
      Bool.and(no_bad(Cli.split_bad(found, attrs, v)), allv(t, found, attrs))

def g_flag(g: Cli.Gather) -> Bool:
  match g:
    case Cli.Gather{seen, +values, count}:
      Bool.and(Laws.read_flags(values),
        Bool.or(Bool.not(seen), Laws.read_one(values)))

def g_count(g: Cli.Gather) -> Bool:
  match g:
    case Cli.Gather{seen, +values, count}:
      Bool.and(Laws.read_counts(values),
        Bool.or(Bool.not(seen), Laws.read_one(values)))

def g_many(g: Cli.Gather, many: Bool, +attrs: List<&2, Cli.Item>) -> Bool:
  match g:
    case Cli.Gather{seen, +values, count}:
      Bool.and(allv(values, Cli.find_delim(attrs), attrs),
        Bool.or(Bool.not(seen), Bool.or(many, Laws.read_one(values))))

def gib(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>, g: Cli.Gather) ->
    Bool:
  match kind:
    case Cli.FlagKind{}: g_flag(g)
    case Cli.CountKind{}: g_count(g)
    case Cli.NegatableKind{}: g_flag(g)
    case Cli.OptionKind{many}: g_many(g, many, attrs)
    case Cli.BareOptionKind{}: g_many(g, False{}, attrs)
    case Cli.PosKind{required, many}: True{}

# A hit for id is valid for an arg of kind and attrs when that arg could
# have made it: a value its attrs accept, or a flag or count hit.
def ev_ok(e: Cli.ScanEvent, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +id: String) -> Bool:
  match e:
    case Cli.ValueHit{k, v}:
      Bool.or(Bool.not(String.eq(k, id)),
        Bool.and(Cli.kind_valued(kind), no_bad(Cli.value_bad(attrs, v))))
    case Cli.FlagHit{k, b}:
      Bool.or(Bool.not(String.eq(k, id)), Cli.kind_flag(kind))
    case Cli.CountHit{k}:
      Bool.or(Bool.not(String.eq(k, id)), Cli.kind_count(kind))
    case Cli.Operand{t}: True{}
    case Cli.Enter{n}: True{}
    case Cli.HelpHit{l}: True{}
    case Cli.VersionHit{}: True{}

def evs_ok(events: List<&2, Cli.ScanEvent>, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +id: String) -> Bool:
  match events:
    case Nil{}: True{}
    case e <> t: Bool.and(ev_ok(e, kind, attrs, id), evs_ok(t, kind, attrs, id))

def many_step(g: Cli.Gather, many: Bool, +attrs: List<&2, Cli.Item>,
    +v: String, nb: {no_bad(Cli.value_bad(attrs, v)) == True{} : Bool},
    ok: {g_many(g, many, attrs) == True{} : Bool}) ->
    {g_many(Cli.gather_value(g, v, many), many, attrs) == True{} : Bool}:
  match g:
    case Cli.Gather{seen, +values, count}:
      match many:
        case True{}:
          and_true(allv(v <> values, Cli.find_delim(attrs), attrs), True{},
            and_true(no_bad(Cli.split_bad(Cli.find_delim(attrs), attrs, v)),
              allv(values, Cli.find_delim(attrs), attrs), nb,
              and_left(allv(values, Cli.find_delim(attrs), attrs),
                Bool.or(Bool.not(seen), True{}), ok)), {==})
        case False{}:
          and_true(Bool.and(no_bad(Cli.value_bad(attrs, v)), True{}), True{},
            and_true(no_bad(Cli.value_bad(attrs, v)), True{}, nb, {==}), {==})

def value_step(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    g: Cli.Gather, +v: String,
    e: {Bool.and(Cli.kind_valued(kind), no_bad(Cli.value_bad(attrs, v)))
      == True{} : Bool},
    ok: {gib(kind, attrs, g) == True{} : Bool}) ->
    {gib(kind, attrs, Cli.gather_value(g, v, Cli.kind_many(kind))) == True{}
      : Bool}:
  match kind:
    case Cli.FlagKind{}:
      Empty.absurd({gib(Cli.FlagKind{}, attrs, Cli.gather_value(g, v,
        False{})) == True{} : Bool}, false_true_absurd(e))
    case Cli.CountKind{}:
      Empty.absurd({gib(Cli.CountKind{}, attrs, Cli.gather_value(g, v,
        False{})) == True{} : Bool}, false_true_absurd(e))
    case Cli.NegatableKind{}:
      Empty.absurd({gib(Cli.NegatableKind{}, attrs, Cli.gather_value(g, v,
        False{})) == True{} : Bool}, false_true_absurd(e))
    case Cli.OptionKind{many}: many_step(g, many, attrs, v, e, ok)
    case Cli.BareOptionKind{}: many_step(g, False{}, attrs, v, e, ok)
    case Cli.PosKind{required, many}: {==}

def value_hit(b: Bool, kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +g: Cli.Gather, +v: String,
    ev: {Bool.or(Bool.not(b), Bool.and(Cli.kind_valued(kind),
      no_bad(Cli.value_bad(attrs, v)))) == True{} : Bool},
    ok: {gib(kind, attrs, g) == True{} : Bool}) ->
    {gib(kind, attrs, Bool.pick(Cli.Gather, b,
      Cli.gather_value(g, v, Cli.kind_many(kind)), g)) == True{} : Bool}:
  match b:
    case True{}: value_step(kind, attrs, g, v, ev, ok)
    case False{}: ok

def flag_g(g: Cli.Gather, b: Bool) ->
    {g_flag(Cli.gather_flag(g, b)) == True{} : Bool}:
  match g:
    case Cli.Gather{seen, values, count}:
      match b:
        case True{}: {==}
        case False{}: {==}

def flag_step(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    g: Cli.Gather, b: Bool, e: {Cli.kind_flag(kind) == True{} : Bool}) ->
    {gib(kind, attrs, Cli.gather_flag(g, b)) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}: flag_g(g, b)
    case Cli.CountKind{}:
      Empty.absurd({gib(Cli.CountKind{}, attrs, Cli.gather_flag(g, b))
        == True{} : Bool}, false_true_absurd(e))
    case Cli.NegatableKind{}: flag_g(g, b)
    case Cli.OptionKind{many}:
      Empty.absurd({gib(Cli.OptionKind{many}, attrs, Cli.gather_flag(g, b))
        == True{} : Bool}, false_true_absurd(e))
    case Cli.BareOptionKind{}:
      Empty.absurd({gib(Cli.BareOptionKind{}, attrs, Cli.gather_flag(g, b))
        == True{} : Bool}, false_true_absurd(e))
    case Cli.PosKind{required, many}: {==}

def flag_hit(b: Bool, kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +g: Cli.Gather, bv: Bool,
    ev: {Bool.or(Bool.not(b), Cli.kind_flag(kind)) == True{} : Bool},
    ok: {gib(kind, attrs, g) == True{} : Bool}) ->
    {gib(kind, attrs, Bool.pick(Cli.Gather, b, Cli.gather_flag(g, bv), g))
      == True{} : Bool}:
  match b:
    case True{}: flag_step(kind, attrs, g, bv, ev)
    case False{}: ok

def count_g(g: Cli.Gather) -> {g_count(Cli.gather_count(g)) == True{} : Bool}:
  match g:
    case Cli.Gather{seen, values, +count}:
      and_true(Bool.and(cnt_ok(Nat.show(Nat.add(count, 1n))), True{}), True{},
        and_true(cnt_ok(Nat.show(Nat.add(count, 1n))), True{},
          show_ok(Nat.add(count, 1n)), {==}), {==})

def count_step(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    g: Cli.Gather, e: {Cli.kind_count(kind) == True{} : Bool}) ->
    {gib(kind, attrs, Cli.gather_count(g)) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}:
      Empty.absurd({gib(Cli.FlagKind{}, attrs, Cli.gather_count(g))
        == True{} : Bool}, false_true_absurd(e))
    case Cli.CountKind{}: count_g(g)
    case Cli.NegatableKind{}:
      Empty.absurd({gib(Cli.NegatableKind{}, attrs, Cli.gather_count(g))
        == True{} : Bool}, false_true_absurd(e))
    case Cli.OptionKind{many}:
      Empty.absurd({gib(Cli.OptionKind{many}, attrs, Cli.gather_count(g))
        == True{} : Bool}, false_true_absurd(e))
    case Cli.BareOptionKind{}:
      Empty.absurd({gib(Cli.BareOptionKind{}, attrs, Cli.gather_count(g))
        == True{} : Bool}, false_true_absurd(e))
    case Cli.PosKind{required, many}: {==}

def count_hit(b: Bool, kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +g: Cli.Gather,
    ev: {Bool.or(Bool.not(b), Cli.kind_count(kind)) == True{} : Bool},
    ok: {gib(kind, attrs, g) == True{} : Bool}) ->
    {gib(kind, attrs, Bool.pick(Cli.Gather, b, Cli.gather_count(g), g))
      == True{} : Bool}:
  match b:
    case True{}: count_step(kind, attrs, g, ev)
    case False{}: ok

def gather_step(e: Cli.ScanEvent, +id: String, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +g: Cli.Gather,
    ok: {gib(kind, attrs, g) == True{} : Bool},
    ev: {ev_ok(e, kind, attrs, id) == True{} : Bool}) ->
    {gib(kind, attrs, Cli.gather_event(e, id, kind, g)) == True{} : Bool}:
  match e:
    case Cli.ValueHit{k, +v}:
      value_hit(String.eq(k, id), kind, attrs, g, v, ev, ok)
    case Cli.FlagHit{k, b}:
      flag_hit(String.eq(k, id), kind, attrs, g, b, ev, ok)
    case Cli.CountHit{k}:
      count_hit(String.eq(k, id), kind, attrs, g, ev, ok)
    case Cli.Operand{t}: ok
    case Cli.Enter{n}: ok
    case Cli.HelpHit{l}: ok
    case Cli.VersionHit{}: ok

def gather_all(events: List<&2, Cli.ScanEvent>, +id: String,
    +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>, +g: Cli.Gather,
    ok: {gib(kind, attrs, g) == True{} : Bool},
    +ev: {evs_ok(events, kind, attrs, id) == True{} : Bool}) ->
    {gib(kind, attrs, Cli.gather_events(events, id, kind, g)) == True{}
      : Bool}:
  match events:
    case Nil{}: ok
    case +e <> +t:
      gather_all(t, id, kind, attrs, Cli.gather_event(e, id, kind, g),
        gather_step(e, id, kind, attrs, g, ok,
          and_left(ev_ok(e, kind, attrs, id), evs_ok(t, kind, attrs, id), ev)),
        and_right(ev_ok(e, kind, attrs, id), evs_ok(t, kind, attrs, id), ev))

def gather_init(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>) ->
    {gib(kind, attrs, Cli.Gather{False{}, [], 0n}) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}: {==}
    case Cli.CountKind{}: {==}
    case Cli.NegatableKind{}: {==}
    case Cli.OptionKind{many}: {==}
    case Cli.BareOptionKind{}: {==}
    case Cli.PosKind{required, many}: {==}

def allv_none(values: List<&2, String>, +attrs: List<&2, Cli.Item>,
    +e: {allv(values, None{}, attrs) == True{} : Bool}) ->
    {Cli.first_bad(values, attrs) == None{} : Maybe<&2, Cli.Bad>}:
  match values:
    case Nil{}: {==}
    case +h <> +t:
      or_none2(Cli.bad_value(Cli.value_reason(attrs, h), h),
        Cli.first_bad(t, attrs),
        no_bad_none(Cli.bad_value(Cli.value_reason(attrs, h), h),
          and_left(no_bad(Cli.bad_value(Cli.value_reason(attrs, h), h)),
            allv(t, None{}, attrs), e)),
        allv_none(t, attrs, and_right(no_bad(Cli.bad_value(Cli.value_reason(
          attrs, h), h)), allv(t, None{}, attrs), e)))

def allv_split(values: List<&2, String>, +sep: Char,
    +attrs: List<&2, Cli.Item>,
    +e: {allv(values, Some{sep}, attrs) == True{} : Bool}) ->
    {Cli.first_bad(Cli.split_each(values, sep), attrs) == None{}
      : Maybe<&2, Cli.Bad>}:
  match values:
    case Nil{}: {==}
    case +h <> +t:
      fb_app(String.split(h, sep), Cli.split_each(t, sep), attrs,
        no_bad_none(Cli.first_bad(String.split(h, sep), attrs),
          and_left(no_bad(Cli.first_bad(String.split(h, sep), attrs)),
            allv(t, Some{sep}, attrs), e)),
        allv_split(t, sep, attrs, and_right(no_bad(Cli.first_bad(
          String.split(h, sep), attrs)), allv(t, Some{sep}, attrs), e)))

# Exactly one value, with r: at most one, and some.
def one_vals(values: List<&2, String>, r: Bool,
    ok: {Bool.and(r, Laws.read_one(values)) == True{} : Bool}) ->
    {Bool.and(Bool.and(r, Laws.read_most_one(values)),
      Bool.not(List.is_empty(&2, String, values))) == True{} : Bool}:
  match values:
    case Nil{}:
      match r:
        case True{}:
          Empty.absurd({Bool.and(Bool.and(True{}, True{}), False{}) == True{}
            : Bool}, false_true_absurd(ok))
        case False{}:
          Empty.absurd({Bool.and(Bool.and(False{}, True{}), False{})
            == True{} : Bool}, false_true_absurd(ok))
    case v <> +t:
      and_true(Bool.and(r, List.is_empty(&2, String, t)), True{}, ok, {==})

def flag_seen(found: Maybe<&2, Char>, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>,
    ok: {Bool.and(Laws.read_flags(values), Laws.read_one(values)) == True{}
      : Bool},
    okl: DelimOk(found, Cli.FlagKind{})) ->
    {fgood(Cli.FlagKind{}, attrs, Cli.apply_delim(found, values)) == True{}
      : Bool}:
  match found:
    case None{}: one_vals(values, Laws.read_flags(values), ok)
    case Some{sep}:
      Empty.absurd({fgood(Cli.FlagKind{}, attrs,
        Cli.apply_delim(Some{sep}, values)) == True{} : Bool},
        false_true_absurd(okl))

def neg_seen(found: Maybe<&2, Char>, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>,
    ok: {Bool.and(Laws.read_flags(values), Laws.read_one(values)) == True{}
      : Bool},
    okl: DelimOk(found, Cli.NegatableKind{})) ->
    {fgood(Cli.NegatableKind{}, attrs, Cli.apply_delim(found, values))
      == True{} : Bool}:
  match found:
    case None{}: one_vals(values, Laws.read_flags(values), ok)
    case Some{sep}:
      Empty.absurd({fgood(Cli.NegatableKind{}, attrs,
        Cli.apply_delim(Some{sep}, values)) == True{} : Bool},
        false_true_absurd(okl))

def count_seen(found: Maybe<&2, Char>, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>,
    ok: {Bool.and(Laws.read_counts(values), Laws.read_one(values)) == True{}
      : Bool},
    okl: DelimOk(found, Cli.CountKind{})) ->
    {fgood(Cli.CountKind{}, attrs, Cli.apply_delim(found, values)) == True{}
      : Bool}:
  match found:
    case None{}: one_vals(values, Laws.read_counts(values), ok)
    case Some{sep}:
      Empty.absurd({fgood(Cli.CountKind{}, attrs,
        Cli.apply_delim(Some{sep}, values)) == True{} : Bool},
        false_true_absurd(okl))

def many_seen(found: Maybe<&2, Char>, +many: Bool, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>,
    ea: {allv(values, found, attrs) == True{} : Bool},
    eo: {Bool.or(many, Laws.read_one(values)) == True{} : Bool},
    okl: DelimMany(found, many)) ->
    {Bool.and(Bool.and(no_bad(Cli.first_bad(Cli.apply_delim(found, values),
        attrs)), Bool.or(many,
        Laws.read_most_one(Cli.apply_delim(found, values)))),
      Bool.or(many, Bool.not(List.is_empty(&2, String,
        Cli.apply_delim(found, values))))) == True{} : Bool}:
  match found:
    case None{}:
      match many:
        case True{}:
          and_true(Bool.and(no_bad(Cli.first_bad(values, attrs)), True{}),
            True{}, and_true(no_bad(Cli.first_bad(values, attrs)), True{},
              nb_of(Cli.first_bad(values, attrs),
                allv_none(values, attrs, ea)), {==}), {==})
        case False{}:
          one_vals(values, no_bad(Cli.first_bad(values, attrs)),
            and_true(no_bad(Cli.first_bad(values, attrs)),
              Laws.read_one(values), nb_of(Cli.first_bad(values, attrs),
                allv_none(values, attrs, ea)), eo))
    case Some{+sep}:
      match many:
        case True{}:
          and_true(Bool.and(no_bad(Cli.first_bad(Cli.split_each(values, sep),
            attrs)), True{}), True{},
            and_true(no_bad(Cli.first_bad(Cli.split_each(values, sep), attrs)),
              True{}, nb_of(Cli.first_bad(Cli.split_each(values, sep), attrs),
                allv_split(values, sep, attrs, ea)), {==}), {==})
        case False{}:
          Empty.absurd({Bool.and(Bool.and(no_bad(Cli.first_bad(
            Cli.split_each(values, sep), attrs)), Bool.or(False{},
            Laws.read_most_one(Cli.split_each(values, sep)))),
            Bool.or(False{}, Bool.not(List.is_empty(&2, String,
              Cli.split_each(values, sep))))) == True{} : Bool},
            false_true_absurd(okl))

# An option the argv names: the values gather kept, split at its delimiter.
def seen_good(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>, -count: Nat,
    +ok: {gib(kind, attrs, Cli.Gather{True{}, values, count}) == True{} : Bool},
    okl: DelimOk(Cli.find_delim(attrs), kind),
    np: {Cli.kind_pos(kind) == False{} : Bool}) ->
    {fgood(kind, attrs, Cli.apply_delim(Cli.find_delim(attrs), values))
      == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}: flag_seen(Cli.find_delim(attrs), attrs, values, ok, okl)
    case Cli.CountKind{}:
      count_seen(Cli.find_delim(attrs), attrs, values, ok, okl)
    case Cli.NegatableKind{}:
      neg_seen(Cli.find_delim(attrs), attrs, values, ok, okl)
    case Cli.OptionKind{+many}:
      many_seen(Cli.find_delim(attrs), many, attrs, values,
        and_left(allv(values, Cli.find_delim(attrs), attrs),
          Bool.or(many, Laws.read_one(values)), ok),
        and_right(allv(values, Cli.find_delim(attrs), attrs),
          Bool.or(many, Laws.read_one(values)), ok),
        delim_many(Cli.find_delim(attrs), Cli.OptionKind{many}, okl))
    case Cli.BareOptionKind{}:
      many_seen(Cli.find_delim(attrs), False{}, attrs, values,
        and_left(allv(values, Cli.find_delim(attrs), attrs),
          Laws.read_one(values), ok),
        and_right(allv(values, Cli.find_delim(attrs), attrs),
          Laws.read_one(values), ok),
        delim_many(Cli.find_delim(attrs), Cli.BareOptionKind{}, okl))
    case Cli.PosKind{required, many}:
      Empty.absurd({fgood(Cli.PosKind{required, many}, attrs,
        Cli.apply_delim(Cli.find_delim(attrs), values)) == True{} : Bool},
        true_false_absurd(np))

# allv holds of xs reversed onto acc when it holds of both.
def allv_rev(xs: List<&2, String>, +acc: List<&2, String>,
    +found: Maybe<&2, Char>, +attrs: List<&2, Cli.Item>,
    +e: {allv(xs, found, attrs) == True{} : Bool},
    ea: {allv(acc, found, attrs) == True{} : Bool}) ->
    {allv(List.reverse.go(&2, String, xs, acc), found, attrs) == True{}
      : Bool}:
  match xs:
    case Nil{}: ea
    case +h <> +t:
      allv_rev(t, h <> acc, found, attrs,
        and_right(no_bad(Cli.split_bad(found, attrs, h)),
          allv(t, found, attrs), e),
        and_true(no_bad(Cli.split_bad(found, attrs, h)),
          allv(acc, found, attrs),
          and_left(no_bad(Cli.split_bad(found, attrs, h)),
            allv(t, found, attrs), e), ea))

# A single value is its own reversal.
def one_rev(xs: List<&2, String>, e: {Laws.read_one(xs) == True{} : Bool}) ->
    {xs == List.reverse(&2, String, xs) : List<&2, String>}:
  match xs:
    case Nil{}: {==}
    case v <> t:
      match t:
        case Nil{}: {==}
        case h <> u:
          Empty.absurd({v <> h <> u == List.reverse(&2, String, v <> h <> u)
            : List<&2, String>}, false_true_absurd(e))

def many_rev(many: Bool, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>, -count: Nat,
    +ok: {g_many(Cli.Gather{True{}, values, count}, many, attrs) == True{}
      : Bool}) ->
    {g_many(Cli.Gather{True{}, List.reverse(&2, String, values), count},
      many, attrs) == True{} : Bool}:
  match many:
    case True{}:
      and_true(allv(List.reverse(&2, String, values), Cli.find_delim(attrs),
        attrs), True{}, allv_rev(values, [], Cli.find_delim(attrs), attrs,
          and_left(allv(values, Cli.find_delim(attrs), attrs), True{}, ok),
          {==}), {==})
    case False{}:
      %one_rev(values, and_right(allv(values, Cli.find_delim(attrs), attrs),
        Laws.read_one(values), ok)) :
        {g_many(Cli.Gather{True{}, _, count}, False{}, attrs) == True{}
          : Bool}
      ok

# gib holds of a seen gather's values in argv order: a repeated option's
# values are each good in any order, and any other arg's are one value.
def rev_gib(kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>, -count: Nat,
    +ok: {gib(kind, attrs, Cli.Gather{True{}, values, count}) == True{}
      : Bool}) ->
    {gib(kind, attrs, Cli.Gather{True{}, List.reverse(&2, String, values),
      count}) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}:
      %one_rev(values, and_right(Laws.read_flags(values),
        Laws.read_one(values), ok)) :
        {g_flag(Cli.Gather{True{}, _, count}) == True{} : Bool}
      ok
    case Cli.CountKind{}:
      %one_rev(values, and_right(Laws.read_counts(values),
        Laws.read_one(values), ok)) :
        {g_count(Cli.Gather{True{}, _, count}) == True{} : Bool}
      ok
    case Cli.NegatableKind{}:
      %one_rev(values, and_right(Laws.read_flags(values),
        Laws.read_one(values), ok)) :
        {g_flag(Cli.Gather{True{}, _, count}) == True{} : Bool}
      ok
    case Cli.OptionKind{many}: many_rev(many, attrs, values, count, ok)
    case Cli.BareOptionKind{}: many_rev(False{}, attrs, values, count, ok)
    case Cli.PosKind{required, many}: {==}

# P21 lists: the args of a scope that have id, and the hits each accepts.

def b_or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) ->
    {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}: {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool},
        false_true_absurd(e))

def b_or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) ->
    {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}: {==}
    case False{}: e

def b_orf_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) ->
    {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false_absurd(e))
    case False{}: {==}

def b_orf_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) ->
    {b == False{} : Bool}:
  match a:
    case True{}: Empty.absurd({b == False{} : Bool}, true_false_absurd(e))
    case False{}: e

def b_or_ff(a: Bool, -b: Bool, ea: {a == False{} : Bool},
    eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({Bool.or(True{}, b) == False{} : Bool},
        true_false_absurd(ea))
    case False{}: eb

def b_not_f(c: Bool, e: {c == False{} : Bool}) ->
    {Bool.not(c) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, true_false_absurd(e))
    case False{}: {==}

def b_not_t(c: Bool, e: {c == True{} : Bool}) ->
    {Bool.not(c) == False{} : Bool}:
  match c:
    case True{}: {==}
    case False{}:
      Empty.absurd({Bool.not(False{}) == False{} : Bool},
        false_true_absurd(e))

# c is false when or(not(c), d) holds and d does not.
def b_ornot(c: Bool, d: Bool, e: {Bool.or(Bool.not(c), d) == True{} : Bool},
    ed: {d == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        true_false_absurd(Equal.trans(Bool, True{}, d, False{},
          Equal.sym(Bool, d, True{}, e), ed)))
    case False{}: {==}

# d is false when or(not(c), not(d)) holds and c does.
def b_nand(c: Bool, d: Bool,
    e: {Bool.or(Bool.not(c), Bool.not(d)) == True{} : Bool},
    ec: {c == True{} : Bool}) -> {d == False{} : Bool}:
  match c:
    case True{}:
      match d:
        case True{}:
          Empty.absurd({True{} == False{} : Bool}, false_true_absurd(e))
        case False{}: {==}
    case False{}:
      Empty.absurd({d == False{} : Bool}, false_true_absurd(ec))

def b_or_assoc(a: Bool, b: Bool, c: Bool) ->
    {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}: {==}
    case False{}: {==}

def b_excl(c: Bool) -> {Bool.or(c, Bool.not(c)) == True{} : Bool}:
  match c:
    case True{}: {==}
    case False{}: {==}

def has(L: List<&2, Cli.Item>, +id: String) -> Bool:
  match L:
    case Nil{}: False{}
    case Cli.Arg{usage, help, attrs} <> tail:
      Bool.or(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        has(tail, id))
    case head <> tail: has(tail, id)

def am1(L: List<&2, Cli.Item>, +id: String) -> Bool:
  match L:
    case Nil{}: True{}
    case Cli.Arg{usage, help, attrs} <> +tail:
      Bool.and(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(usage,
        attrs)), id)), Bool.not(has(tail, id))), am1(tail, id))
    case head <> tail: am1(tail, id)

def nonpos(L: List<&2, Cli.Item>) -> Bool:
  match L:
    case Nil{}: True{}
    case Cli.Arg{usage, help, attrs} <> tail:
      Bool.and(Bool.not(Cli.kind_pos(Cli.info_kind(Cli.arg_info(usage,
        attrs)))), nonpos(tail))
    case head <> tail: nonpos(tail)

# A hit event names an id other than id; other events name none.
def off(e: Cli.ScanEvent, +id: String) -> Bool:
  match e:
    case Cli.FlagHit{k, b}: Bool.not(String.eq(k, id))
    case Cli.CountHit{k}: Bool.not(String.eq(k, id))
    case Cli.ValueHit{k, v}: Bool.not(String.eq(k, id))
    case Cli.Operand{t}: True{}
    case Cli.Enter{n}: True{}
    case Cli.HelpHit{l}: True{}
    case Cli.VersionHit{}: True{}

def ok_at(+info: Cli.ArgInfo, e: Cli.ScanEvent, +id: String) -> Bool:
  Bool.or(Bool.not(String.eq(Cli.info_id(info), id)),
    ev_ok(e, Cli.info_kind(info), Cli.info_attrs(info), id))

# Every arg of L with id accepts e.
def acc(L: List<&2, Cli.Item>, +e: Cli.ScanEvent, +id: String) -> Bool:
  match L:
    case Nil{}: True{}
    case Cli.Arg{usage, help, attrs} <> tail:
      Bool.and(ok_at(Cli.arg_info(usage, attrs), e, id), acc(tail, e, id))
    case head <> tail: acc(tail, e, id)

def ev_all(events: List<&2, Cli.ScanEvent>, +L: List<&2, Cli.Item>,
    +id: String) -> Bool:
  match events:
    case Nil{}: True{}
    case e <> tail: Bool.and(acc(L, e, id), ev_all(tail, L, id))

def off_ev(e: Cli.ScanEvent, -kind: Cli.UsageKind,
    -attrs: List<&2, Cli.Item>, +id: String,
    eo: {off(e, id) == True{} : Bool}) ->
    {ev_ok(e, kind, attrs, id) == True{} : Bool}:
  match e:
    case Cli.FlagHit{k, b}:
      b_or_l(Bool.not(String.eq(k, id)), Cli.kind_flag(kind), eo)
    case Cli.CountHit{k}:
      b_or_l(Bool.not(String.eq(k, id)), Cli.kind_count(kind), eo)
    case Cli.ValueHit{k, v}:
      b_or_l(Bool.not(String.eq(k, id)), Bool.and(Cli.kind_valued(kind),
        no_bad(Cli.value_bad(attrs, v))), eo)
    case Cli.Operand{t}: {==}
    case Cli.Enter{n}: {==}
    case Cli.HelpHit{l}: {==}
    case Cli.VersionHit{}: {==}

def ok_off(+info: Cli.ArgInfo, e: Cli.ScanEvent, +id: String,
    eo: {off(e, id) == True{} : Bool}) ->
    {ok_at(info, e, id) == True{} : Bool}:
  b_or_r(Bool.not(String.eq(Cli.info_id(info), id)),
    ev_ok(e, Cli.info_kind(info), Cli.info_attrs(info), id),
    off_ev(e, Cli.info_kind(info), Cli.info_attrs(info), id, eo))

def ok_none(+info: Cli.ArgInfo, -e: Cli.ScanEvent, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    {ok_at(info, e, id) == True{} : Bool}:
  b_or_l(Bool.not(String.eq(Cli.info_id(info), id)),
    ev_ok(e, Cli.info_kind(info), Cli.info_attrs(info), id),
    b_not_f(String.eq(Cli.info_id(info), id), ec))

# Every arg accepts an event off id.
def acc_off(L: List<&2, Cli.Item>, +e: Cli.ScanEvent, +id: String,
    +eo: {off(e, id) == True{} : Bool}) -> {acc(L, e, id) == True{} : Bool}:
  match L:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      and_true(ok_at(Cli.arg_info(usage, attrs), e, id), acc(tail, e, id),
        ok_off(Cli.arg_info(usage, attrs), e, id, eo),
        acc_off(tail, e, id, eo))
    case Cli.Sub{x0, x1, x2} <> tail: acc_off(tail, e, id, eo)
    case Cli.Version{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Alias{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Hidden{} <> tail: acc_off(tail, e, id, eo)
    case Cli.Example{x0, x1} <> tail: acc_off(tail, e, id, eo)
    case Cli.After{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.SubOptional{} <> tail: acc_off(tail, e, id, eo)
    case Cli.External{} <> tail: acc_off(tail, e, id, eo)
    case Cli.Exclusive{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.NeedOne{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Id{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Required{} <> tail: acc_off(tail, e, id, eo)
    case Cli.AttrDefault{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.AttrEnv{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Global{} <> tail: acc_off(tail, e, id, eo)
    case Cli.Heading{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.As{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.OneOf{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Delim{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Hyphen{} <> tail: acc_off(tail, e, id, eo)
    case Cli.Rest{} <> tail: acc_off(tail, e, id, eo)
    case Cli.Bare{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Conflicts{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Requires{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Group{x0} <> tail: acc_off(tail, e, id, eo)
    case Cli.Builtin{} <> tail: acc_off(tail, e, id, eo)

# A list with no arg of id accepts every event.
def acc_none(L: List<&2, Cli.Item>, +e: Cli.ScanEvent, +id: String,
    +en: {has(L, id) == False{} : Bool}) ->
    {acc(L, e, id) == True{} : Bool}:
  match L:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      and_true(ok_at(Cli.arg_info(usage, attrs), e, id), acc(tail, e, id),
        ok_none(Cli.arg_info(usage, attrs), e, id,
          b_orf_l(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
            has(tail, id), en)),
        acc_none(tail, e, id,
          b_orf_r(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
            has(tail, id), en)))
    case Cli.Sub{x0, x1, x2} <> tail: acc_none(tail, e, id, en)
    case Cli.Version{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Alias{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Hidden{} <> tail: acc_none(tail, e, id, en)
    case Cli.Example{x0, x1} <> tail: acc_none(tail, e, id, en)
    case Cli.After{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.SubOptional{} <> tail: acc_none(tail, e, id, en)
    case Cli.External{} <> tail: acc_none(tail, e, id, en)
    case Cli.Exclusive{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.NeedOne{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Id{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Required{} <> tail: acc_none(tail, e, id, en)
    case Cli.AttrDefault{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.AttrEnv{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Global{} <> tail: acc_none(tail, e, id, en)
    case Cli.Heading{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.As{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.OneOf{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Delim{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Hyphen{} <> tail: acc_none(tail, e, id, en)
    case Cli.Rest{} <> tail: acc_none(tail, e, id, en)
    case Cli.Bare{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Conflicts{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Requires{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Group{x0} <> tail: acc_none(tail, e, id, en)
    case Cli.Builtin{} <> tail: acc_none(tail, e, id, en)

def has_app(xs: List<&2, Cli.Item>, +ys: List<&2, Cli.Item>, +id: String) ->
    {has(List.append(&2, Cli.Item, xs, ys), id)
      == Bool.or(has(xs, id), has(ys, id)) : Bool}:
  match xs:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      Equal.trans(Bool,
        Bool.or(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
          has(List.append(&2, Cli.Item, tail, ys), id)),
        Bool.or(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
          Bool.or(has(tail, id), has(ys, id))),
        Bool.or(Bool.or(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)),
          id), has(tail, id)), has(ys, id)),
        Equal.cong(Bool, Bool,
          x => Bool.or(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
            x),
          has(List.append(&2, Cli.Item, tail, ys), id),
          Bool.or(has(tail, id), has(ys, id)), has_app(tail, ys, id)),
        b_or_assoc(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
          has(tail, id), has(ys, id)))
    case Cli.Sub{x0, x1, x2} <> tail: has_app(tail, ys, id)
    case Cli.Version{x0} <> tail: has_app(tail, ys, id)
    case Cli.Alias{x0} <> tail: has_app(tail, ys, id)
    case Cli.Hidden{} <> tail: has_app(tail, ys, id)
    case Cli.Example{x0, x1} <> tail: has_app(tail, ys, id)
    case Cli.After{x0} <> tail: has_app(tail, ys, id)
    case Cli.SubOptional{} <> tail: has_app(tail, ys, id)
    case Cli.External{} <> tail: has_app(tail, ys, id)
    case Cli.Exclusive{x0} <> tail: has_app(tail, ys, id)
    case Cli.NeedOne{x0} <> tail: has_app(tail, ys, id)
    case Cli.Id{x0} <> tail: has_app(tail, ys, id)
    case Cli.Required{} <> tail: has_app(tail, ys, id)
    case Cli.AttrDefault{x0} <> tail: has_app(tail, ys, id)
    case Cli.AttrEnv{x0} <> tail: has_app(tail, ys, id)
    case Cli.Global{} <> tail: has_app(tail, ys, id)
    case Cli.Heading{x0} <> tail: has_app(tail, ys, id)
    case Cli.As{x0} <> tail: has_app(tail, ys, id)
    case Cli.OneOf{x0} <> tail: has_app(tail, ys, id)
    case Cli.Delim{x0} <> tail: has_app(tail, ys, id)
    case Cli.Hyphen{} <> tail: has_app(tail, ys, id)
    case Cli.Rest{} <> tail: has_app(tail, ys, id)
    case Cli.Bare{x0} <> tail: has_app(tail, ys, id)
    case Cli.Conflicts{x0} <> tail: has_app(tail, ys, id)
    case Cli.Requires{x0} <> tail: has_app(tail, ys, id)
    case Cli.Group{x0} <> tail: has_app(tail, ys, id)
    case Cli.Builtin{} <> tail: has_app(tail, ys, id)

def has_app_f(+xs: List<&2, Cli.Item>, +ys: List<&2, Cli.Item>, +id: String,
    ex: {has(xs, id) == False{} : Bool}, ey: {has(ys, id) == False{} : Bool})
    -> {has(List.append(&2, Cli.Item, xs, ys), id) == False{} : Bool}:
  %Equal.sym(Bool, has(List.append(&2, Cli.Item, xs, ys), id),
    Bool.or(has(xs, id), has(ys, id)), has_app(xs, ys, id)) :
    {_ == False{} : Bool}
  b_or_ff(has(xs, id), has(ys, id), ex, ey)

def has_app_t(xs: List<&2, Cli.Item>, +ys: List<&2, Cli.Item>, +id: String,
    e: {Bool.or(has(xs, id), has(ys, id)) == True{} : Bool}) ->
    {has(List.append(&2, Cli.Item, xs, ys), id) == True{} : Bool}:
  %Equal.sym(Bool, has(List.append(&2, Cli.Item, xs, ys), id),
    Bool.or(has(xs, id), has(ys, id)), has_app(xs, ys, id)) :
    {_ == True{} : Bool}
  e

# am1 over an Arg: what the arg's own id and the rest give.
def am1_head(c: Bool, ht: Bool, hy: Bool,
    p: {Bool.or(Bool.not(c), Bool.not(ht)) == True{} : Bool},
    d: {Bool.or(Bool.not(Bool.or(c, ht)), Bool.not(hy)) == True{} : Bool}) ->
    {Bool.or(Bool.not(c), Bool.not(Bool.or(ht, hy))) == True{} : Bool}:
  match c:
    case False{}: {==}
    case True{}:
      match ht:
        case True{}:
          Empty.absurd({Bool.or(Bool.not(True{}), Bool.not(Bool.or(True{},
            hy))) == True{} : Bool}, false_true_absurd(p))
        case False{}:
          match hy:
            case True{}:
              Empty.absurd({Bool.or(Bool.not(True{}), Bool.not(Bool.or(
                False{}, True{}))) == True{} : Bool}, false_true_absurd(d))
            case False{}: {==}

def am1_rest(c: Bool, ht: Bool, hy: Bool,
    d: {Bool.or(Bool.not(Bool.or(c, ht)), Bool.not(hy)) == True{} : Bool}) ->
    {Bool.or(Bool.not(ht), Bool.not(hy)) == True{} : Bool}:
  match c:
    case True{}:
      match ht:
        case False{}: {==}
        case True{}: d
    case False{}:
      match ht:
        case False{}: {==}
        case True{}: d

def am1_arg(+x: Cli.ArgInfo, +tail: List<&2, Cli.Item>,
    +ys: List<&2, Cli.Item>, +id: String,
    ax: {Bool.and(Bool.or(Bool.not(String.eq(Cli.info_id(x), id)),
      Bool.not(has(tail, id))), am1(tail, id)) == True{} : Bool},
    +d: {Bool.or(Bool.not(Bool.or(String.eq(Cli.info_id(x), id),
      has(tail, id))), Bool.not(has(ys, id))) == True{} : Bool},
    ih: {Bool.or(Bool.not(has(tail, id)), Bool.not(has(ys, id))) == True{}
      : Bool} -> {am1(List.append(&2, Cli.Item, tail, ys), id) == True{}
      : Bool}) ->
    {Bool.and(Bool.or(Bool.not(String.eq(Cli.info_id(x), id)),
      Bool.not(has(List.append(&2, Cli.Item, tail, ys), id))),
      am1(List.append(&2, Cli.Item, tail, ys), id)) == True{} : Bool}:
  +c = String.eq(Cli.info_id(x), id)
  %Equal.sym(Bool, has(List.append(&2, Cli.Item, tail, ys), id),
    Bool.or(has(tail, id), has(ys, id)), has_app(tail, ys, id)) :
    {Bool.and(Bool.or(Bool.not(c), Bool.not(_)),
      am1(List.append(&2, Cli.Item, tail, ys), id)) == True{} : Bool}
  and_true(Bool.or(Bool.not(c), Bool.not(Bool.or(has(tail, id),
    has(ys, id)))), am1(List.append(&2, Cli.Item, tail, ys), id),
    am1_head(c, has(tail, id), has(ys, id),
      and_left(Bool.or(Bool.not(c), Bool.not(has(tail, id))),
        am1(tail, id), ax), d),
    ih(am1_rest(c, has(tail, id), has(ys, id), d)))

def am1_app(xs: List<&2, Cli.Item>, +ys: List<&2, Cli.Item>, +id: String,
    +ax: {am1(xs, id) == True{} : Bool}, +ay: {am1(ys, id) == True{} : Bool},
    d: {Bool.or(Bool.not(has(xs, id)), Bool.not(has(ys, id))) == True{}
      : Bool}) ->
    {am1(List.append(&2, Cli.Item, xs, ys), id) == True{} : Bool}:
  match xs:
    case Nil{}: ay
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      am1_arg(Cli.arg_info(usage, attrs), tail, ys, id, ax, d,
        dt => am1_app(tail, ys, id,
          and_right(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(
            usage, attrs)), id)), Bool.not(has(tail, id))), am1(tail, id),
            ax), ay, dt))
    case Cli.Sub{x0, x1, x2} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Version{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Alias{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Hidden{} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Example{x0, x1} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.After{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.SubOptional{} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.External{} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Exclusive{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.NeedOne{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Id{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Required{} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.AttrDefault{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.AttrEnv{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Global{} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Heading{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.As{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.OneOf{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Delim{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Hyphen{} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Rest{} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Bare{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Conflicts{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Requires{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Group{x0} <> tail: am1_app(tail, ys, id, ax, ay, d)
    case Cli.Builtin{} <> tail: am1_app(tail, ys, id, ax, ay, d)

def has_glob_pick(g: Bool, +usage: String, -help: String,
    +attrs: List<&2, Cli.Item>, +gt: List<&2, Cli.Item>, +id: String,
    ec: {String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id) == False{}
      : Bool}, ih: {has(gt, id) == False{} : Bool}) ->
    {has(Bool.pick(List<&2, Cli.Item>, g, Cli.Arg{usage, help, attrs} <> gt,
      gt), id) == False{} : Bool}:
  match g:
    case True{}:
      b_or_ff(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        has(gt, id), ec, ih)
    case False{}: ih

# A list's globals have no arg of id when the list has none.
def has_glob_go(L: List<&2, Cli.Item>, +all: List<&2, Cli.Item>, +id: String,
    +e: {has(L, id) == False{} : Bool}) ->
    {has(Cli.global_go(L, all), id) == False{} : Bool}:
  match L:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      has_glob_pick(Cli.has_global(attrs), usage, help, attrs,
        Cli.global_go(tail, all), id,
        b_orf_l(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
          has(tail, id), e),
        has_glob_go(tail, all, id,
          b_orf_r(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
            has(tail, id), e)))
    case Cli.Sub{x0, x1, x2} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Version{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Alias{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Hidden{} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Example{x0, x1} <> tail: has_glob_go(tail, all, id, e)
    case Cli.After{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.SubOptional{} <> tail: has_glob_go(tail, all, id, e)
    case Cli.External{} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Exclusive{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {has(G, id) == False{} : Bool},
        Cli.Exclusive{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        has_glob_go(tail, all, id, e), has_glob_go(tail, all, id, e))
    case Cli.NeedOne{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {has(G, id) == False{} : Bool},
        Cli.NeedOne{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        has_glob_go(tail, all, id, e), has_glob_go(tail, all, id, e))
    case Cli.Id{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Required{} <> tail: has_glob_go(tail, all, id, e)
    case Cli.AttrDefault{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.AttrEnv{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Global{} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Heading{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.As{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.OneOf{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Delim{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Hyphen{} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Rest{} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Bare{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Conflicts{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Requires{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Group{x0} <> tail: has_glob_go(tail, all, id, e)
    case Cli.Builtin{} <> tail: has_glob_go(tail, all, id, e)

def has_glob(+L: List<&2, Cli.Item>, +id: String,
    +e: {has(L, id) == False{} : Bool}) ->
    {has(Cli.global_items(L), id) == False{} : Bool}:
  has_glob_go(L, L, id, e)

def am1_glob_c(c: Bool, ht: Bool, hg: Bool,
    p: {Bool.or(Bool.not(c), Bool.not(ht)) == True{} : Bool},
    m: {ht == False{} : Bool} -> {hg == False{} : Bool}) ->
    {Bool.or(Bool.not(c), Bool.not(hg)) == True{} : Bool}:
  match c:
    case False{}: {==}
    case True{}:
      match ht:
        case True{}:
          Empty.absurd({Bool.or(Bool.not(True{}), Bool.not(hg)) == True{}
            : Bool}, false_true_absurd(p))
        case False{}: b_not_f(hg, m({==}))

def am1_glob_pick(g: Bool, +usage: String, -help: String,
    +attrs: List<&2, Cli.Item>, +gt: List<&2, Cli.Item>, +id: String,
    p: {Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)),
      id)), Bool.not(has(gt, id))) == True{} : Bool},
    ih: {am1(gt, id) == True{} : Bool}) ->
    {am1(Bool.pick(List<&2, Cli.Item>, g, Cli.Arg{usage, help, attrs} <> gt,
      gt), id) == True{} : Bool}:
  match g:
    case True{}:
      and_true(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(usage,
        attrs)), id)), Bool.not(has(gt, id))), am1(gt, id), p, ih)
    case False{}: ih

def am1_glob_go(L: List<&2, Cli.Item>, +all: List<&2, Cli.Item>, +id: String,
    +a: {am1(L, id) == True{} : Bool}) ->
    {am1(Cli.global_go(L, all), id) == True{} : Bool}:
  match L:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      am1_glob_pick(Cli.has_global(attrs), usage, help, attrs,
        Cli.global_go(tail, all), id,
        am1_glob_c(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
          has(tail, id), has(Cli.global_go(tail, all), id),
          and_left(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(usage,
            attrs)), id)), Bool.not(has(tail, id))), am1(tail, id), a),
          ht => has_glob_go(tail, all, id, ht)),
        am1_glob_go(tail, all, id,
          and_right(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(
            usage, attrs)), id)), Bool.not(has(tail, id))), am1(tail, id), a)))
    case Cli.Sub{x0, x1, x2} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Version{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Alias{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Hidden{} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Example{x0, x1} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.After{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.SubOptional{} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.External{} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Exclusive{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {am1(G, id) == True{} : Bool},
        Cli.Exclusive{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        am1_glob_go(tail, all, id, a), am1_glob_go(tail, all, id, a))
    case Cli.NeedOne{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {am1(G, id) == True{} : Bool},
        Cli.NeedOne{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        am1_glob_go(tail, all, id, a), am1_glob_go(tail, all, id, a))
    case Cli.Id{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Required{} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.AttrDefault{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.AttrEnv{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Global{} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Heading{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.As{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.OneOf{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Delim{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Hyphen{} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Rest{} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Bare{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Conflicts{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Requires{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Group{x0} <> tail: am1_glob_go(tail, all, id, a)
    case Cli.Builtin{} <> tail: am1_glob_go(tail, all, id, a)

def am1_glob(+L: List<&2, Cli.Item>, +id: String,
    +a: {am1(L, id) == True{} : Bool}) ->
    {am1(Cli.global_items(L), id) == True{} : Bool}:
  am1_glob_go(L, L, id, a)

def nonpos_app(xs: List<&2, Cli.Item>, +ys: List<&2, Cli.Item>,
    +nx: {nonpos(xs) == True{} : Bool}, ny: {nonpos(ys) == True{} : Bool}) ->
    {nonpos(List.append(&2, Cli.Item, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}: ny
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      and_true(Bool.not(Cli.kind_pos(Cli.info_kind(Cli.arg_info(usage,
        attrs)))), nonpos(List.append(&2, Cli.Item, tail, ys)),
        and_left(Bool.not(Cli.kind_pos(Cli.info_kind(Cli.arg_info(usage,
          attrs)))), nonpos(tail), nx),
        nonpos_app(tail, ys, and_right(Bool.not(Cli.kind_pos(Cli.info_kind(
          Cli.arg_info(usage, attrs)))), nonpos(tail), nx), ny))
    case Cli.Sub{x0, x1, x2} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Version{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Alias{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Hidden{} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Example{x0, x1} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.After{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.SubOptional{} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.External{} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Exclusive{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.NeedOne{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Id{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Required{} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.AttrDefault{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.AttrEnv{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Global{} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Heading{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.As{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.OneOf{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Delim{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Hyphen{} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Rest{} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Bare{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Conflicts{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Requires{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Group{x0} <> tail: nonpos_app(tail, ys, nx, ny)
    case Cli.Builtin{} <> tail: nonpos_app(tail, ys, nx, ny)

def acc_app(xs: List<&2, Cli.Item>, +ys: List<&2, Cli.Item>,
    +e: Cli.ScanEvent, +id: String, +ax: {acc(xs, e, id) == True{} : Bool},
    ay: {acc(ys, e, id) == True{} : Bool}) ->
    {acc(List.append(&2, Cli.Item, xs, ys), e, id) == True{} : Bool}:
  match xs:
    case Nil{}: ay
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      and_true(ok_at(Cli.arg_info(usage, attrs), e, id),
        acc(List.append(&2, Cli.Item, tail, ys), e, id),
        and_left(ok_at(Cli.arg_info(usage, attrs), e, id), acc(tail, e, id),
          ax),
        acc_app(tail, ys, e, id, and_right(ok_at(Cli.arg_info(usage, attrs),
          e, id), acc(tail, e, id), ax), ay))
    case Cli.Sub{x0, x1, x2} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Version{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Alias{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Hidden{} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Example{x0, x1} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.After{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.SubOptional{} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.External{} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Exclusive{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.NeedOne{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Id{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Required{} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.AttrDefault{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.AttrEnv{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Global{} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Heading{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.As{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.OneOf{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Delim{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Hyphen{} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Rest{} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Bare{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Conflicts{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Requires{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Group{x0} <> tail: acc_app(tail, ys, e, id, ax, ay)
    case Cli.Builtin{} <> tail: acc_app(tail, ys, e, id, ax, ay)

def acc_glob_pick(g: Bool, +usage: String, -help: String,
    +attrs: List<&2, Cli.Item>, +gt: List<&2, Cli.Item>, +e: Cli.ScanEvent,
    +id: String, p: {ok_at(Cli.arg_info(usage, attrs), e, id) == True{}
      : Bool}, ih: {acc(gt, e, id) == True{} : Bool}) ->
    {acc(Bool.pick(List<&2, Cli.Item>, g, Cli.Arg{usage, help, attrs} <> gt,
      gt), e, id) == True{} : Bool}:
  match g:
    case True{}:
      and_true(ok_at(Cli.arg_info(usage, attrs), e, id), acc(gt, e, id), p,
        ih)
    case False{}: ih

def acc_glob_go(L: List<&2, Cli.Item>, +all: List<&2, Cli.Item>, +e: Cli.ScanEvent,
    +id: String, +a: {acc(L, e, id) == True{} : Bool}) ->
    {acc(Cli.global_go(L, all), e, id) == True{} : Bool}:
  match L:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      acc_glob_pick(Cli.has_global(attrs), usage, help, attrs,
        Cli.global_go(tail, all), e, id,
        and_left(ok_at(Cli.arg_info(usage, attrs), e, id), acc(tail, e, id),
          a),
        acc_glob_go(tail, all, e, id, and_right(ok_at(Cli.arg_info(usage, attrs), e,
          id), acc(tail, e, id), a)))
    case Cli.Sub{x0, x1, x2} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Version{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Alias{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Hidden{} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Example{x0, x1} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.After{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.SubOptional{} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.External{} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Exclusive{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {acc(G, e, id) == True{} : Bool},
        Cli.Exclusive{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        acc_glob_go(tail, all, e, id, a), acc_glob_go(tail, all, e, id, a))
    case Cli.NeedOne{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {acc(G, e, id) == True{} : Bool},
        Cli.NeedOne{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        acc_glob_go(tail, all, e, id, a), acc_glob_go(tail, all, e, id, a))
    case Cli.Id{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Required{} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.AttrDefault{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.AttrEnv{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Global{} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Heading{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.As{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.OneOf{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Delim{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Hyphen{} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Rest{} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Bare{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Conflicts{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Requires{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Group{x0} <> tail: acc_glob_go(tail, all, e, id, a)
    case Cli.Builtin{} <> tail: acc_glob_go(tail, all, e, id, a)

def acc_glob(+L: List<&2, Cli.Item>, +e: Cli.ScanEvent, +id: String,
    +a: {acc(L, e, id) == True{} : Bool}) ->
    {acc(Cli.global_items(L), e, id) == True{} : Bool}:
  acc_glob_go(L, L, e, id, a)

def ev_app(events: List<&2, Cli.ScanEvent>, +xs: List<&2, Cli.Item>,
    +ys: List<&2, Cli.Item>, +id: String,
    +ex: {ev_all(events, xs, id) == True{} : Bool},
    +ey: {ev_all(events, ys, id) == True{} : Bool}) ->
    {ev_all(events, List.append(&2, Cli.Item, xs, ys), id) == True{} : Bool}:
  match events:
    case Nil{}: {==}
    case +e <> +tail:
      and_true(acc(List.append(&2, Cli.Item, xs, ys), e, id),
        ev_all(tail, List.append(&2, Cli.Item, xs, ys), id),
        acc_app(xs, ys, e, id,
          and_left(acc(xs, e, id), ev_all(tail, xs, id), ex),
          and_left(acc(ys, e, id), ev_all(tail, ys, id), ey)),
        ev_app(tail, xs, ys, id,
          and_right(acc(xs, e, id), ev_all(tail, xs, id), ex),
          and_right(acc(ys, e, id), ev_all(tail, ys, id), ey)))

def ev_glob(events: List<&2, Cli.ScanEvent>, +L: List<&2, Cli.Item>,
    +id: String, +ev: {ev_all(events, L, id) == True{} : Bool}) ->
    {ev_all(events, Cli.global_items(L), id) == True{} : Bool}:
  match events:
    case Nil{}: {==}
    case +e <> +tail:
      and_true(acc(Cli.global_items(L), e, id),
        ev_all(tail, Cli.global_items(L), id),
        acc_glob(L, e, id, and_left(acc(L, e, id), ev_all(tail, L, id), ev)),
        ev_glob(tail, L, id, and_right(acc(L, e, id), ev_all(tail, L, id),
          ev)))

def kept_step(b: Bool, +e: Cli.ScanEvent, +rest: List<&2, Cli.ScanEvent>,
    +L: List<&2, Cli.Item>, +id: String,
    ok: {Bool.or(Bool.not(b), acc(L, e, id)) == True{} : Bool},
    ih: {ev_all(rest, L, id) == True{} : Bool}) ->
    {ev_all(Cli.events_kept(b, e, rest), L, id) == True{} : Bool}:
  match b:
    case True{}: and_true(acc(L, e, id), ev_all(rest, L, id), ok, ih)
    case False{}: ih

# L accepts each event the scan keeps on entering a subcommand.
def kacc(events: List<&2, Cli.ScanEvent>, +globals: List<&2, Cli.SpecItem>,
    +L: List<&2, Cli.Item>, +id: String) -> Bool:
  match events:
    case Nil{}: True{}
    case +e <> tail:
      Bool.and(Bool.or(Bool.not(Cli.event_inherited(Cli.event_id(e),
        globals)), acc(L, e, id)), kacc(tail, globals, L, id))

def ev_kept(events: List<&2, Cli.ScanEvent>, +globals: List<&2, Cli.SpecItem>,
    +L: List<&2, Cli.Item>, +id: String,
    +k: {kacc(events, globals, L, id) == True{} : Bool}) ->
    {ev_all(Cli.events_inherited(events, globals), L, id) == True{} : Bool}:
  match events:
    case Nil{}: {==}
    case +e <> +tail:
      kept_step(Cli.event_inherited(Cli.event_id(e), globals), e,
        Cli.events_inherited(tail, globals), L, id,
        and_left(Bool.or(Bool.not(Cli.event_inherited(Cli.event_id(e),
          globals)), acc(L, e, id)), kacc(tail, globals, L, id), k),
        ev_kept(tail, globals, L, id,
          and_right(Bool.or(Bool.not(Cli.event_inherited(Cli.event_id(e),
            globals)), acc(L, e, id)), kacc(tail, globals, L, id), k)))

def kacc_all(events: List<&2, Cli.ScanEvent>,
    +globals: List<&2, Cli.SpecItem>, +L: List<&2, Cli.Item>, +id: String,
    +ev: {ev_all(events, L, id) == True{} : Bool}) ->
    {kacc(events, globals, L, id) == True{} : Bool}:
  match events:
    case Nil{}: {==}
    case +e <> +tail:
      and_true(Bool.or(Bool.not(Cli.event_inherited(Cli.event_id(e),
        globals)), acc(L, e, id)), kacc(tail, globals, L, id),
        b_or_r(Bool.not(Cli.event_inherited(Cli.event_id(e), globals)),
          acc(L, e, id), and_left(acc(L, e, id), ev_all(tail, L, id), ev)),
        kacc_all(tail, globals, L, id,
          and_right(acc(L, e, id), ev_all(tail, L, id), ev)))

def b_imp(c: Bool, d: Bool,
    e: {Bool.or(Bool.not(c), d) == True{} : Bool},
    ec: {c == True{} : Bool}) -> {d == True{} : Bool}:
  match c:
    case True{}: e
    case False{}:
      Empty.absurd({d == True{} : Bool}, false_true_absurd(ec))

def info_or(m: Maybe<&2, Cli.ArgInfo>, +d: Cli.ArgInfo) -> Cli.ArgInfo:
  match m:
    case None{}: d
    case Some{x}: x

def some_inj(-a: Cli.ArgInfo, -b: Cli.ArgInfo,
    e: {Some{a} == Some{b} : Maybe<&2, Cli.ArgInfo>}) ->
    {a == b : Cli.ArgInfo}:
  Equal.cong(Maybe<&2, Cli.ArgInfo>, Cli.ArgInfo, m => info_or(m, a),
    Some{a}, Some{b}, e)

def some_none_absurd(-a: Cli.ArgInfo,
    e: {Some{a} == None{} : Maybe<&2, Cli.ArgInfo>}) -> Empty:
  true_false_absurd(Equal.cong(Maybe<&2, Cli.ArgInfo>, Bool,
    m => Maybe.is_some(&2, Cli.ArgInfo, m), Some{a}, None{}, e))

def arg_none_some(-a: Cli.ArgInfo,
    e: {None{} == Some{a} : Maybe<&2, Cli.ArgInfo>}) -> Empty:
  false_true_absurd(Equal.cong(Maybe<&2, Cli.ArgInfo>, Bool,
    m => Maybe.is_some(&2, Cli.ArgInfo, m), None{}, Some{a}, e))

def ref_pick(c: Bool, -info: Cli.ArgInfo, -r: Maybe<&2, Cli.ArgInfo>,
    -h: Bool, e: {Maybe.is_some(&2, Cli.ArgInfo, r) == h : Bool}) ->
    {Maybe.is_some(&2, Cli.ArgInfo, Bool.pick(Maybe<&2, Cli.ArgInfo>, c,
      Some{info}, r)) == Bool.or(c, h) : Bool}:
  match c:
    case True{}: {==}
    case False{}: e

# arg_ref finds an arg exactly when has says L has one.
def ref_has(L: List<&2, Cli.Item>, +id: String) ->
    {Maybe.is_some(&2, Cli.ArgInfo, Laws.arg_ref(L, id)) == has(L, id) : Bool}:
  match L:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      ref_pick(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), Laws.arg_ref(tail, id), has(tail, id),
        ref_has(tail, id))
    case Cli.Sub{x0, x1, x2} <> tail: ref_has(tail, id)
    case Cli.Version{x0} <> tail: ref_has(tail, id)
    case Cli.Alias{x0} <> tail: ref_has(tail, id)
    case Cli.Hidden{} <> tail: ref_has(tail, id)
    case Cli.Example{x0, x1} <> tail: ref_has(tail, id)
    case Cli.After{x0} <> tail: ref_has(tail, id)
    case Cli.SubOptional{} <> tail: ref_has(tail, id)
    case Cli.External{} <> tail: ref_has(tail, id)
    case Cli.Exclusive{x0} <> tail: ref_has(tail, id)
    case Cli.NeedOne{x0} <> tail: ref_has(tail, id)
    case Cli.Id{x0} <> tail: ref_has(tail, id)
    case Cli.Required{} <> tail: ref_has(tail, id)
    case Cli.AttrDefault{x0} <> tail: ref_has(tail, id)
    case Cli.AttrEnv{x0} <> tail: ref_has(tail, id)
    case Cli.Global{} <> tail: ref_has(tail, id)
    case Cli.Heading{x0} <> tail: ref_has(tail, id)
    case Cli.As{x0} <> tail: ref_has(tail, id)
    case Cli.OneOf{x0} <> tail: ref_has(tail, id)
    case Cli.Delim{x0} <> tail: ref_has(tail, id)
    case Cli.Hyphen{} <> tail: ref_has(tail, id)
    case Cli.Rest{} <> tail: ref_has(tail, id)
    case Cli.Bare{x0} <> tail: ref_has(tail, id)
    case Cli.Conflicts{x0} <> tail: ref_has(tail, id)
    case Cli.Requires{x0} <> tail: ref_has(tail, id)
    case Cli.Group{x0} <> tail: ref_has(tail, id)
    case Cli.Builtin{} <> tail: ref_has(tail, id)

def ref_none_m(m: Maybe<&2, Cli.ArgInfo>, -h: Bool,
    e: {Maybe.is_some(&2, Cli.ArgInfo, m) == h : Bool},
    eh: {h == False{} : Bool}) ->
    {m == None{} : Maybe<&2, Cli.ArgInfo>}:
  match m:
    case None{}: {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, Cli.ArgInfo>},
        true_false_absurd(Equal.trans(Bool, True{}, h, False{}, e, eh)))

def ref_none(+L: List<&2, Cli.Item>, +id: String,
    e: {has(L, id) == False{} : Bool}) ->
    {Laws.arg_ref(L, id) == None{} : Maybe<&2, Cli.ArgInfo>}:
  ref_none_m(Laws.arg_ref(L, id), has(L, id), ref_has(L, id), e)

def ref_some_m(m: Maybe<&2, Cli.ArgInfo>, -h: Bool, -r: Cli.ArgInfo,
    e: {Maybe.is_some(&2, Cli.ArgInfo, m) == h : Bool},
    er: {m == Some{r} : Maybe<&2, Cli.ArgInfo>}) -> {h == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({h == True{} : Bool}, arg_none_some(r, er))
    case Some{x}: Equal.sym(Bool, True{}, h, e)

def ref_found(+L: List<&2, Cli.Item>, +id: String, -r: Cli.ArgInfo,
    er: {Laws.arg_ref(L, id) == Some{r} : Maybe<&2, Cli.ArgInfo>}) ->
    {has(L, id) == True{} : Bool}:
  ref_some_m(Laws.arg_ref(L, id), has(L, id), r, ref_has(L, id), er)

def ref_app_pick(c: Bool, -info: Cli.ArgInfo,
    -x: Maybe<&2, Cli.ArgInfo>, -y: Maybe<&2, Cli.ArgInfo>,
    -xy: Maybe<&2, Cli.ArgInfo>,
    e: {xy == Maybe.or(&2, Cli.ArgInfo, x, y) : Maybe<&2, Cli.ArgInfo>}) ->
    {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info}, xy)
      == Maybe.or(&2, Cli.ArgInfo, Bool.pick(Maybe<&2, Cli.ArgInfo>, c,
        Some{info}, x), y) : Maybe<&2, Cli.ArgInfo>}:
  match c:
    case True{}: {==}
    case False{}: e

# arg_ref over xs ++ ys answers from xs first, then from ys.
def ref_app(xs: List<&2, Cli.Item>, +ys: List<&2, Cli.Item>, +id: String) ->
    {Laws.arg_ref(List.append(&2, Cli.Item, xs, ys), id)
      == Maybe.or(&2, Cli.ArgInfo, Laws.arg_ref(xs, id), Laws.arg_ref(ys, id))
      : Maybe<&2, Cli.ArgInfo>}:
  match xs:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      ref_app_pick(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), Laws.arg_ref(tail, id), Laws.arg_ref(ys, id),
        Laws.arg_ref(List.append(&2, Cli.Item, tail, ys), id), ref_app(tail, ys, id))
    case Cli.Sub{x0, x1, x2} <> tail: ref_app(tail, ys, id)
    case Cli.Version{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Alias{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Hidden{} <> tail: ref_app(tail, ys, id)
    case Cli.Example{x0, x1} <> tail: ref_app(tail, ys, id)
    case Cli.After{x0} <> tail: ref_app(tail, ys, id)
    case Cli.SubOptional{} <> tail: ref_app(tail, ys, id)
    case Cli.External{} <> tail: ref_app(tail, ys, id)
    case Cli.Exclusive{x0} <> tail: ref_app(tail, ys, id)
    case Cli.NeedOne{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Id{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Required{} <> tail: ref_app(tail, ys, id)
    case Cli.AttrDefault{x0} <> tail: ref_app(tail, ys, id)
    case Cli.AttrEnv{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Global{} <> tail: ref_app(tail, ys, id)
    case Cli.Heading{x0} <> tail: ref_app(tail, ys, id)
    case Cli.As{x0} <> tail: ref_app(tail, ys, id)
    case Cli.OneOf{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Delim{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Hyphen{} <> tail: ref_app(tail, ys, id)
    case Cli.Rest{} <> tail: ref_app(tail, ys, id)
    case Cli.Bare{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Conflicts{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Requires{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Group{x0} <> tail: ref_app(tail, ys, id)
    case Cli.Builtin{} <> tail: ref_app(tail, ys, id)

def acc_ref_pick(c: Bool, +info: Cli.ArgInfo, -rest: Maybe<&2, Cli.ArgInfo>,
    +e: Cli.ScanEvent, +id: String, -r: Cli.ArgInfo,
    ec: {String.eq(Cli.info_id(info), id) == c : Bool},
    ok: {ok_at(info, e, id) == True{} : Bool},
    er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info}, rest) == Some{r}
      : Maybe<&2, Cli.ArgInfo>},
    ih: {rest == Some{r} : Maybe<&2, Cli.ArgInfo>} ->
      {ev_ok(e, Cli.info_kind(r), Cli.info_attrs(r), id) == True{} : Bool}) ->
    {ev_ok(e, Cli.info_kind(r), Cli.info_attrs(r), id) == True{} : Bool}:
  match c:
    case True{}:
      %some_inj(info, r, er) : {ev_ok(e, Cli.info_kind(_),
        Cli.info_attrs(_), id) == True{} : Bool}
      b_imp(String.eq(Cli.info_id(info), id), ev_ok(e, Cli.info_kind(info),
        Cli.info_attrs(info), id), ok, ec)
    case False{}: ih(er)

# The arg arg_ref finds in L accepts each event L accepts.
def acc_ref(L: List<&2, Cli.Item>, +e: Cli.ScanEvent, +id: String,
    -r: Cli.ArgInfo, +a: {acc(L, e, id) == True{} : Bool},
    er: {Laws.arg_ref(L, id) == Some{r} : Maybe<&2, Cli.ArgInfo>}) ->
    {ev_ok(e, Cli.info_kind(r), Cli.info_attrs(r), id) == True{} : Bool}:
  match L:
    case Nil{}:
      Empty.absurd({ev_ok(e, Cli.info_kind(r), Cli.info_attrs(r), id)
        == True{} : Bool}, arg_none_some(r, er))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      acc_ref_pick(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), Laws.arg_ref(tail, id), e, id, r, {==},
        and_left(ok_at(Cli.arg_info(usage, attrs), e, id), acc(tail, e, id),
          a), er,
        et => acc_ref(tail, e, id, r, and_right(ok_at(Cli.arg_info(usage,
          attrs), e, id), acc(tail, e, id), a), et))
    case Cli.Sub{x0, x1, x2} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Version{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Alias{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Hidden{} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Example{x0, x1} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.After{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.SubOptional{} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.External{} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Exclusive{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.NeedOne{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Id{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Required{} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.AttrDefault{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.AttrEnv{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Global{} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Heading{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.As{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.OneOf{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Delim{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Hyphen{} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Rest{} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Bare{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Conflicts{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Requires{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Group{x0} <> tail: acc_ref(tail, e, id, r, a, er)
    case Cli.Builtin{} <> tail: acc_ref(tail, e, id, r, a, er)

def ev_ref(events: List<&2, Cli.ScanEvent>, +L: List<&2, Cli.Item>,
    +id: String, +r: Cli.ArgInfo,
    +ev: {ev_all(events, L, id) == True{} : Bool},
    +er: {Laws.arg_ref(L, id) == Some{r} : Maybe<&2, Cli.ArgInfo>}) ->
    {evs_ok(events, Cli.info_kind(r), Cli.info_attrs(r), id) == True{}
      : Bool}:
  match events:
    case Nil{}: {==}
    case +e <> +tail:
      and_true(ev_ok(e, Cli.info_kind(r), Cli.info_attrs(r), id),
        evs_ok(tail, Cli.info_kind(r), Cli.info_attrs(r), id),
        acc_ref(L, e, id, r, and_left(acc(L, e, id), ev_all(tail, L, id), ev),
          er),
        ev_ref(tail, L, id, r, and_right(acc(L, e, id), ev_all(tail, L, id),
          ev), er))

def ev_rev_go(xs: List<&2, Cli.ScanEvent>, +acc_l: List<&2, Cli.ScanEvent>,
    +L: List<&2, Cli.Item>, +id: String,
    +ex: {ev_all(xs, L, id) == True{} : Bool},
    ea: {ev_all(acc_l, L, id) == True{} : Bool}) ->
    {ev_all(List.reverse.go(&2, Cli.ScanEvent, xs, acc_l), L, id) == True{}
      : Bool}:
  match xs:
    case Nil{}: ea
    case +h <> +t:
      ev_rev_go(t, h <> acc_l, L, id,
        and_right(acc(L, h, id), ev_all(t, L, id), ex),
        and_true(acc(L, h, id), ev_all(acc_l, L, id),
          and_left(acc(L, h, id), ev_all(t, L, id), ex), ea))

def ev_rev(xs: List<&2, Cli.ScanEvent>, +L: List<&2, Cli.Item>, +id: String,
    ex: {ev_all(xs, L, id) == True{} : Bool}) ->
    {ev_all(List.reverse(&2, Cli.ScanEvent, xs), L, id) == True{} : Bool}:
  ev_rev_go(xs, Nil{}, L, id, ex, {==})

# P21 lint tree: what lint checks of a scope's items that the scan reads, as
# one Bool (qt), which no def is barred from using twice. sh: whether seen
# holds an arg id x.

def sh(seen: List<&2, Cli.Seen>, +x: String) -> Bool:
  match seen:
    case Nil{}: False{}
    case Cli.SeenArg{old, s, l} <> tail:
      Bool.or(String.eq(x, old), sh(tail, x))
    case Cli.SeenSub{n} <> tail: sh(tail, x)
    case Cli.SeenArgAlias{n} <> tail: sh(tail, x)
    case Cli.SeenSubAlias{n} <> tail: sh(tail, x)

def argq(parsed: Cli.Usage, +attrs: List<&2, Cli.Item>,
    +seen: List<&2, Cli.Seen>) -> Bool:
  match parsed:
    case Cli.Invalid{col}: False{}
    case Cli.Parsed{d, s, l, k}:
      Bool.and(Bool.not(sh(seen, Cli.use_id(Cli.find_id(attrs), d))),
        Bool.or(Bool.not(Cli.has_global(attrs)), Bool.not(Cli.kind_pos(k))))

def qt(items: List<&2, Cli.Item>, +seen: List<&2, Cli.Seen>,
    +inh: List<&2, Cli.Seen>) -> Bool:
  match items:
    case Nil{}: True{}
    case Cli.Arg{+usage, help, +attrs} <> tail:
      Bool.and(argq(Cli.parse_usage(usage), attrs, seen),
        qt(tail, List.append(&2, Cli.Seen,
          Cli.arg_entries(Cli.parse_usage(usage), attrs), seen), inh))
    case Cli.Sub{+name, about, +children} <> tail:
      Bool.and(Bool.not(Cli.sub_collision(seen, name)),
        Bool.and(qt(children, inh, List.append(&2, Cli.Seen,
          Cli.global_entries(Cli.lint_items(children)), inh)),
          qt(tail, List.append(&2, Cli.Seen,
            Cli.sub_alias_entries(Cli.find_aliases(children)),
            Cli.SeenSub{name} <> seen), inh)))
    case head <> tail: qt(tail, seen, inh)

def nt_f(c: Bool, e: {Bool.not(c) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true_absurd(e))
    case False{}: {==}

def b_nand2(c: Bool, d: Bool,
    e: {Bool.or(Bool.not(c), Bool.not(d)) == True{} : Bool},
    ed: {d == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      match d:
        case True{}:
          Empty.absurd({True{} == False{} : Bool}, false_true_absurd(e))
        case False{}:
          Empty.absurd({True{} == False{} : Bool}, false_true_absurd(ed))
    case False{}: {==}

def b_weak(h: Bool, +a: Bool, +b: Bool,
    e: {Bool.or(Bool.not(h), Bool.not(Bool.or(a, b))) == True{} : Bool}) ->
    {Bool.or(Bool.not(h), Bool.not(b)) == True{} : Bool}:
  match h:
    case True{}: b_not_f(b, b_orf_r(a, b, nt_f(Bool.or(a, b), e)))
    case False{}: {==}

def b_notnot(c: Bool) -> {Bool.or(Bool.not(c), c) == True{} : Bool}:
  match c:
    case True{}: {==}
    case False{}: {==}

def b_or_mid(a: Bool, c: Bool, -b: Bool,
    e: {Bool.or(Bool.not(a), b) == True{} : Bool}) ->
    {Bool.or(Bool.not(a), Bool.or(c, b)) == True{} : Bool}:
  match a:
    case True{}: b_or_r(c, b, e)
    case False{}: {==}

def eq_flip(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) ->
    {String.eq(b, a) == True{} : Bool}:
  %eq_reflect(a, b, e) : {String.eq(_, a) == True{} : Bool}
  string_eq_refl(a)

def eq_flip_c(c: Bool, +a: String, +b: String,
    ec: {String.eq(b, a) == c : Bool},
    e: {String.eq(a, b) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        true_false_absurd(Equal.trans(Bool, True{}, String.eq(a, b), False{},
          Equal.sym(Bool, String.eq(a, b), True{}, eq_flip(b, a, ec)), e)))
    case False{}: {==}

def eq_flip_f(+a: String, +b: String, e: {String.eq(a, b) == False{} : Bool})
    -> {String.eq(b, a) == False{} : Bool}:
  eq_flip_c(String.eq(b, a), a, b, {==}, e)

def text_false(+a: String, +b: String,
    e: {Cli.same_text(a, b) == False{} : Bool}) ->
    {String.eq(a, b) == False{} : Bool}:
  Equal.trans(Bool, String.eq(a, b), Cli.same_text(a, b), False{},
    Equal.sym(Bool, Cli.same_text(a, b), String.eq(a, b), Laws.p18_text(a, b)),
    e)

def sh_tr(-S: List<&2, Cli.Seen>, +a: String, +b: String,
    e: {String.eq(a, b) == True{} : Bool},
    n: {sh(S, a) == False{} : Bool}) -> {sh(S, b) == False{} : Bool}:
  %eq_reflect(a, b, e) : {sh(S, _) == False{} : Bool}
  n

# What lint's arg and subcommand problems being empty give qt.

def help_dup(h: Bool, c: Bool, -at: String, -name: String,
    e: {Bool.pick(List<&2, Cli.Problem>, h, [Cli.Reserved{at, name}],
      Cli.when_problem(c, Cli.Dup{at, name})) == Nil{}
      : List<&2, Cli.Problem>}) -> {Bool.not(c) == True{} : Bool}:
  match h:
    case True{}:
      Empty.absurd({Bool.not(c) == True{} : Bool},
        plist_cons_absurd(Cli.Reserved{at, name}, Nil{}, e))
    case False{}:
      match c:
        case True{}:
          Empty.absurd({Bool.not(True{}) == True{} : Bool},
            plist_cons_absurd(Cli.Dup{at, name}, Nil{}, e))
        case False{}: {==}

def rd_pick(r: Bool, m: Maybe<&2, String>, -at: String, -long: String,
    e: {Bool.pick(List<&2, Cli.Problem>, r, [Cli.Reserved{at, long}],
      Cli.maybe_dup(m, at)) == Nil{} : List<&2, Cli.Problem>}) ->
    {m == None{} : Maybe<&2, String>}:
  match r:
    case True{}:
      Empty.absurd({m == None{} : Maybe<&2, String>},
        plist_cons_absurd(Cli.Reserved{at, long}, Nil{}, e))
    case False{}:
      match m:
        case None{}: {==}
        case Some{x}:
          Empty.absurd({Some{x} == None{} : Maybe<&2, String>},
            plist_cons_absurd(Cli.Dup{at, x}, Nil{}, e))

def mor_l(m: Maybe<&2, String>, -n: Maybe<&2, String>,
    e: {Maybe.or(&2, String, m, n) == None{} : Maybe<&2, String>}) ->
    {m == None{} : Maybe<&2, String>}:
  match m:
    case None{}: {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, String>},
        why_some_absurd(x, e))

def mor_r(m: Maybe<&2, String>, -n: Maybe<&2, String>,
    e: {Maybe.or(&2, String, m, n) == None{} : Maybe<&2, String>}) ->
    {n == None{} : Maybe<&2, String>}:
  match m:
    case None{}: e
    case Some{x}:
      Empty.absurd({n == None{} : Maybe<&2, String>}, why_some_absurd(x, e))

def here_none(a: Bool, b: Bool, c: Bool, -short: String, -long: String,
    -id: String,
    e: {Bool.pick(Maybe<&2, String>, a, Some{short},
      Bool.pick(Maybe<&2, String>, b, Some{long},
        Bool.pick(Maybe<&2, String>, c, Some{id}, None{}))) == None{}
      : Maybe<&2, String>}) -> {c == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({c == False{} : Bool}, why_some_absurd(short, e))
    case False{}:
      match b:
        case True{}:
          Empty.absurd({c == False{} : Bool}, why_some_absurd(long, e))
        case False{}:
          match c:
            case True{}:
              Empty.absurd({True{} == False{} : Bool}, why_some_absurd(id, e))
            case False{}: {==}

def alias_rest(a: Bool, b: Bool, -short: String, -long: String,
    -m: Maybe<&2, String>,
    e: {Bool.pick(Maybe<&2, String>, a, Some{short},
      Bool.pick(Maybe<&2, String>, b, Some{long}, m)) == None{}
      : Maybe<&2, String>}) -> {m == None{} : Maybe<&2, String>}:
  match a:
    case True{}:
      Empty.absurd({m == None{} : Maybe<&2, String>},
        why_some_absurd(short, e))
    case False{}:
      match b:
        case True{}:
          Empty.absurd({m == None{} : Maybe<&2, String>},
            why_some_absurd(long, e))
        case False{}: e

# No collision with seen: seen holds no arg of that id.
def coll_sh(seen: List<&2, Cli.Seen>, +id: String, +short: String,
    +long: String,
    +e: {Cli.arg_collision(seen, id, short, long) == None{}
      : Maybe<&2, String>}) -> {sh(seen, id) == False{} : Bool}:
  match seen:
    case Nil{}: {==}
    case Cli.SeenArg{+oi, +os, +ol} <> +tail:
      b_or_ff(String.eq(id, oi), sh(tail, id),
        text_false(id, oi, here_none(Cli.same_nonempty(short, os),
          Cli.same_nonempty(long, ol), Cli.same_text(id, oi), short, long, id,
          mor_l(Bool.pick(Maybe<&2, String>, Cli.same_nonempty(short, os),
            Some{short}, Bool.pick(Maybe<&2, String>,
              Cli.same_nonempty(long, ol), Some{long},
              Bool.pick(Maybe<&2, String>, Cli.same_text(id, oi), Some{id},
                None{}))), Cli.arg_collision(tail, id, short, long), e))),
        coll_sh(tail, id, short, long,
          mor_r(Bool.pick(Maybe<&2, String>, Cli.same_nonempty(short, os),
            Some{short}, Bool.pick(Maybe<&2, String>,
              Cli.same_nonempty(long, ol), Some{long},
              Bool.pick(Maybe<&2, String>, Cli.same_text(id, oi), Some{id},
                None{}))), Cli.arg_collision(tail, id, short, long), e)))
    case Cli.SeenSub{n} <> tail: coll_sh(tail, id, short, long, e)
    case Cli.SeenArgAlias{+old} <> tail:
      coll_sh(tail, id, short, long,
        alias_rest(Cli.same_nonempty(short, old), Cli.same_nonempty(long, old),
          short, long, Cli.arg_collision(tail, id, short, long), e))
    case Cli.SeenSubAlias{n} <> tail: coll_sh(tail, id, short, long, e)

def glob_hit(c: Bool, -at: String, -rest: List<&2, Cli.Problem>,
    e: {List.append(&2, Cli.Problem,
      Cli.maybe_misplaced(Cli.bad_attr(c, "global"), at), rest) == Nil{}
      : List<&2, Cli.Problem>}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool},
        plist_cons_absurd(Cli.Misplaced{at, "global"}, rest, e))
    case False{}: {==}

# A global arg isn't positional, as placement_issues checks.
def glob_place(attrs: List<&2, Cli.Item>, +kind: Cli.UsageKind, +at: String,
    +e: {Cli.placement_issues(attrs, kind, at) == Nil{}
      : List<&2, Cli.Problem>}) ->
    {Bool.or(Bool.not(Cli.has_global(attrs)), Bool.not(Cli.kind_pos(kind)))
      == True{} : Bool}:
  match attrs:
    case Nil{}: {==}
    case Cli.Global{} <> +tail:
      glob_hit(Cli.kind_pos(kind), at, Cli.placement_issues(tail, kind, at), e)
    case Cli.Arg{x0, x1, x2} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Arg{x0, x1, x2}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Sub{x0, x1, x2} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Sub{x0, x1, x2}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Version{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Version{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Alias{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Alias{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Hidden{} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Hidden{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Example{x0, x1} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Example{x0, x1}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.After{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.After{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.SubOptional{} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.SubOptional{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.External{} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.External{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Exclusive{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Exclusive{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.NeedOne{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.NeedOne{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Id{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Id{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Required{} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Required{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.AttrDefault{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.AttrDefault{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.AttrEnv{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.AttrEnv{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Heading{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Heading{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.As{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.As{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.OneOf{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.OneOf{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Delim{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Delim{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Hyphen{} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Hyphen{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Rest{} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Rest{}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Bare{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Bare{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Conflicts{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Conflicts{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Requires{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Requires{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Group{x0} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Group{x0}, kind), at), Cli.placement_issues(tail, kind, at), e))
    case Cli.Builtin{} <> +tail: glob_place(tail, kind, at, app_nil_right(Cli.maybe_misplaced(Cli.misplaced_attr_name(Cli.Builtin{}, kind), at), Cli.placement_issues(tail, kind, at), e))

def argq_take(+kind: Cli.UsageKind, +id: String, +short: String,
    +long: String, +usage: String, +help: String, +attrs: List<&2, Cli.Item>,
    +remaining: List<&2, Cli.LintItem>, +at: String, +ids: List<&2, String>,
    +seen: List<&2, Cli.Seen>, +optional: Bool, +variadic: Bool,
    +version: Bool,
    parts: AllNil(issue_list(kind, id, short, long, usage, help, attrs,
      remaining, at, ids, seen, optional, variadic, version))) ->
    {Bool.and(Bool.not(sh(seen, id)), Bool.or(Bool.not(Cli.has_global(attrs)),
      Bool.not(Cli.kind_pos(kind)))) == True{} : Bool}:
  (e1, r1) = parts
  (e2, r2) = r1
  and_true(Bool.not(sh(seen, id)),
    Bool.or(Bool.not(Cli.has_global(attrs)), Bool.not(Cli.kind_pos(kind))),
    b_not_f(sh(seen, id), coll_sh(seen, id, short, long,
      rd_pick(Bool.or(String.eq(long, "--help"), Bool.and(version,
        String.eq(long, "--version"))), Cli.arg_collision(seen, id, short,
        long), at, long, e1))),
    glob_place(attrs, kind, at, app_nil_left(Cli.placement_issues(attrs,
      kind, at), Cli.duplicate_type_issues(Cli.value_type_names(attrs), at),
      e2)))

def argq_of(parsed: Cli.Usage, +usage: String, +help: String,
    +attrs: List<&2, Cli.Item>, +remaining: List<&2, Cli.LintItem>,
    +at: String, +ids: List<&2, String>, +seen: List<&2, Cli.Seen>,
    +optional: Bool, +variadic: Bool, +version: Bool,
    e: {Cli.arg_problems(parsed, usage, help, attrs, remaining, at, ids, seen,
      optional, variadic, version) == Nil{} : List<&2, Cli.Problem>}) ->
    {argq(parsed, attrs, seen) == True{} : Bool}:
  match parsed:
    case Cli.Invalid{+col}:
      Empty.absurd({argq(Cli.Invalid{col}, attrs, seen) == True{} : Bool},
        plist_cons_absurd(Cli.BadUsage{at, usage, col},
          Cli.when_problem(Bool.and(String.is_empty(help),
            Bool.not(Cli.has_hidden(attrs))), Cli.NoHelp{at, usage}), e))
    case Cli.Parsed{+derived, +short, +long, +kind}:
      argq_take(kind, Cli.use_id(Cli.find_id(attrs), derived), short, long,
        usage, help, attrs, remaining, at, ids, seen, optional, variadic,
        version, concat_all(issue_list(kind, Cli.use_id(Cli.find_id(attrs),
        derived), short, long, usage, help, attrs, remaining, at, ids, seen,
        optional, variadic, version), app_nil_left(Cli.arg_issues(kind,
          Cli.use_id(Cli.find_id(attrs), derived), short, long, usage, help,
          attrs, remaining, at, ids, seen, optional, variadic, version),
          Cli.arg_alias_issues(Cli.find_aliases(attrs), at,
            Cli.SeenArg{Cli.use_id(Cli.find_id(attrs), derived), short, long}
              <> seen, version), e)))

def qsub(+name: String, +about: String, +children: List<&2, Cli.Item>,
    +tail: List<&2, Cli.Item>, +at: String, +ids: List<&2, String>,
    +seen: List<&2, Cli.Seen>, +inherited: List<&2, Cli.Seen>,
    +optional: Bool, +variadic: Bool, +version: Bool, +root: Bool,
    parts: AllNil(sub_list(name, about, children, Cli.lint_items(children),
      Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic,
      version, root)),
    ih_c: {Cli.lint(Cli.lint_items(children), String.concat([at, " ", name]),
      Cli.scope_ids(Cli.lint_items(children)), inherited,
      List.append(&2, Cli.Seen, Cli.global_entries(Cli.lint_items(children)),
        inherited), False{}, False{}, version, False{}) == Nil{}
      : List<&2, Cli.Problem>} ->
      {qt(children, inherited, List.append(&2, Cli.Seen,
        Cli.global_entries(Cli.lint_items(children)), inherited)) == True{}
        : Bool},
    ih_t: {Cli.lint(Cli.lint_items(tail), at, ids, List.append(&2, Cli.Seen,
      Cli.sub_alias_entries(Cli.find_aliases(children)),
      Cli.SeenSub{name} <> seen), inherited, optional, variadic, version, root)
      == Nil{} : List<&2, Cli.Problem>} ->
      {qt(tail, List.append(&2, Cli.Seen,
        Cli.sub_alias_entries(Cli.find_aliases(children)),
        Cli.SeenSub{name} <> seen), inherited) == True{} : Bool}) ->
    {qt(Cli.Sub{name, about, children} <> tail, seen, inherited) == True{}
      : Bool}:
  (e1, r1) = parts
  (e2, r2) = r1
  (e3, r3) = r2
  (e4, r4) = r3
  (e5, r5) = r4
  and_true(Bool.not(Cli.sub_collision(seen, name)),
    Bool.and(qt(children, inherited, List.append(&2, Cli.Seen,
      Cli.global_entries(Cli.lint_items(children)), inherited)),
      qt(tail, List.append(&2, Cli.Seen,
        Cli.sub_alias_entries(Cli.find_aliases(children)),
        Cli.SeenSub{name} <> seen), inherited)),
    help_dup(String.eq(name, "help"), Cli.sub_collision(seen, name), at, name,
      app_nil_right(Cli.when_problem(Bool.not(Cli.valid_command_name(name)),
        Cli.BadName{at, name}), Bool.pick(List<&2, Cli.Problem>,
        String.eq(name, "help"), [Cli.Reserved{at, name}],
        Cli.when_problem(Cli.sub_collision(seen, name), Cli.Dup{at, name})),
        e1)),
    and_true(qt(children, inherited, List.append(&2, Cli.Seen,
      Cli.global_entries(Cli.lint_items(children)), inherited)),
      qt(tail, List.append(&2, Cli.Seen,
        Cli.sub_alias_entries(Cli.find_aliases(children)),
        Cli.SeenSub{name} <> seen), inherited), ih_c(e4), ih_t(e5)))

# lint finding nothing in items: the tree qt holds of them.
def qtree(items: List<&2, Cli.Item>, +at: String, +ids: List<&2, String>,
    +seen: List<&2, Cli.Seen>, +inherited: List<&2, Cli.Seen>,
    +optional: Bool, +variadic: Bool, +version: Bool, +root: Bool,
    +e: {Cli.lint(Cli.lint_items(items), at, ids, seen, inherited, optional,
      variadic, version, root) == Nil{} : List<&2, Cli.Problem>}) ->
    {qt(items, seen, inherited) == True{} : Bool}:
  match items:
    case Nil{}: {==}
    case Cli.Arg{+usage, +help, +attrs} <> +tail:
      and_true(argq(Cli.parse_usage(usage), attrs, seen),
        qt(tail, List.append(&2, Cli.Seen,
          Cli.arg_entries(Cli.parse_usage(usage), attrs), seen), inherited),
        argq_of(Cli.parse_usage(usage), usage, help, attrs,
          Cli.lint_items(tail), at, ids, seen, optional, variadic, version,
          app_nil_left(Cli.arg_problems(Cli.parse_usage(usage), usage, help, attrs, Cli.lint_items(tail), at, ids, seen, optional, variadic, version), Cli.lint(Cli.lint_items(tail), at, ids, List.append(&2, Cli.Seen, Cli.arg_entries(Cli.parse_usage(usage), attrs), seen), inherited, Bool.or(optional, Cli.usage_kind(~Cli.kind_optional_pos, Cli.parse_usage(usage))), Bool.or(variadic, Cli.usage_kind(~Cli.kind_variadic_pos, Cli.parse_usage(usage))), version, root), e)),
        qtree(tail, at, ids, List.append(&2, Cli.Seen, Cli.arg_entries(Cli.parse_usage(usage), attrs), seen), inherited, Bool.or(optional, Cli.usage_kind(~Cli.kind_optional_pos, Cli.parse_usage(usage))), Bool.or(variadic, Cli.usage_kind(~Cli.kind_variadic_pos, Cli.parse_usage(usage))), version, root, app_nil_right(Cli.arg_problems(Cli.parse_usage(usage), usage, help, attrs, Cli.lint_items(tail), at, ids, seen, optional, variadic, version), Cli.lint(Cli.lint_items(tail), at, ids, List.append(&2, Cli.Seen, Cli.arg_entries(Cli.parse_usage(usage), attrs), seen), inherited, Bool.or(optional, Cli.usage_kind(~Cli.kind_optional_pos, Cli.parse_usage(usage))), Bool.or(variadic, Cli.usage_kind(~Cli.kind_variadic_pos, Cli.parse_usage(usage))), version, root), e)))
    case Cli.Sub{+name, +about, +children} <> +tail:
      qsub(name, about, children, tail, at, ids, seen, inherited, optional, variadic, version, root,
        concat_all(sub_list(name, about, children, Cli.lint_items(children),
          Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e),
        ec => qtree(children, String.concat([at, " ", name]), Cli.scope_ids(Cli.lint_items(children)), inherited, List.append(&2, Cli.Seen, Cli.global_entries(Cli.lint_items(children)), inherited), False{}, False{}, version, False{}, ec),
        et => qtree(tail, at, ids, List.append(&2, Cli.Seen, Cli.sub_alias_entries(Cli.find_aliases(children)), Cli.SeenSub{name} <> seen), inherited, optional, variadic, version, root, et))
    case Cli.Version{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Version{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Alias{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Alias{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Hidden{} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Hidden{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Example{x0, x1} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Example{x0, x1}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.After{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.After{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.SubOptional{} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.SubOptional{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.External{} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.External{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Exclusive{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Exclusive{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.NeedOne{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.NeedOne{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Id{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Id{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Required{} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Required{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.AttrDefault{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.AttrDefault{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.AttrEnv{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.AttrEnv{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Global{} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Global{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Heading{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Heading{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.As{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.As{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.OneOf{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.OneOf{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Delim{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Delim{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Hyphen{} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Hyphen{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Rest{} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Rest{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Bare{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Bare{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Conflicts{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Conflicts{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Requires{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Requires{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Group{x0} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Group{x0}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))
    case Cli.Builtin{} <> +tail: qtree(tail, at, ids, seen, inherited, optional, variadic, version, root, app_nil_right(Cli.maybe_misplaced(Cli.command_attr_name(Cli.Builtin{}, root), at), Cli.lint(Cli.lint_items(tail), at, ids, seen, inherited, optional, variadic, version, root), e))

# What qt gives: at most one arg of id in items, none if seen holds one
# (qam); seen's globals cover the items' global args (gcov); no global is
# positional (gnonpos); and the subcommand a query finds is the one its own
# name finds, with its children's tree (canon).

def sh_sub(xs: List<&2, String>, +n: String, +S: List<&2, Cli.Seen>,
    +x: String) ->
    {sh(List.append(&2, Cli.Seen, Cli.sub_alias_entries(xs),
      Cli.SeenSub{n} <> S), x) == sh(S, x) : Bool}:
  match xs:
    case Nil{}: {==}
    case a <> t: sh_sub(t, n, S, x)

def sh_alias(xs: List<&2, String>, +S: List<&2, Cli.Seen>, +x: String) ->
    {sh(List.append(&2, Cli.Seen, Cli.arg_alias_entries(xs), S), x)
      == sh(S, x) : Bool}:
  match xs:
    case Nil{}: {==}
    case a <> t: sh_alias(t, S, x)

def sh_up(xs: List<&2, Cli.Seen>, +ys: List<&2, Cli.Seen>, +x: String) ->
    {Bool.or(Bool.not(sh(ys, x)), sh(List.append(&2, Cli.Seen, xs, ys), x))
      == True{} : Bool}:
  match xs:
    case Nil{}: b_notnot(sh(ys, x))
    case Cli.SeenArg{+old, s, l} <> +tail:
      b_or_mid(sh(ys, x), String.eq(x, old),
        sh(List.append(&2, Cli.Seen, tail, ys), x), sh_up(tail, ys, x))
    case Cli.SeenSub{n} <> tail: sh_up(tail, ys, x)
    case Cli.SeenArgAlias{n} <> tail: sh_up(tail, ys, x)
    case Cli.SeenSubAlias{n} <> tail: sh_up(tail, ys, x)

def qam_w(+t: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    +al: List<&2, Cli.Seen>, +X: String, +id: String,
    sal: {sh(List.append(&2, Cli.Seen, al, S), id) == sh(S, id) : Bool},
    e: {Bool.or(Bool.not(has(t, id)), Bool.not(Bool.or(String.eq(id, X),
      sh(List.append(&2, Cli.Seen, al, S), id)))) == True{} : Bool}) ->
    {Bool.or(Bool.not(has(t, id)), Bool.not(sh(S, id))) == True{} : Bool}:
  %sal : {Bool.or(Bool.not(has(t, id)), Bool.not(_)) == True{} : Bool}
  b_weak(has(t, id), String.eq(id, X),
    sh(List.append(&2, Cli.Seen, al, S), id), e)

def qam_c(c: Bool, +X: String, +s: String, +l: String,
    +t: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>, +al: List<&2, Cli.Seen>,
    +id: String, +ec: {String.eq(X, id) == c : Bool},
    ns: {sh(S, X) == False{} : Bool},
    +ih: {Bool.and(am1(t, id), Bool.or(Bool.not(has(t, id)),
      Bool.not(sh(Cli.SeenArg{X, s, l} <> List.append(&2, Cli.Seen, al, S),
        id)))) == True{} : Bool},
    sal: {sh(List.append(&2, Cli.Seen, al, S), id) == sh(S, id) : Bool}) ->
    {Bool.and(Bool.and(Bool.or(Bool.not(c), Bool.not(has(t, id))),
      am1(t, id)), Bool.or(Bool.not(Bool.or(c, has(t, id))),
      Bool.not(sh(S, id)))) == True{} : Bool}:
  match c:
    case True{}:
      and_true(Bool.and(Bool.not(has(t, id)), am1(t, id)),
        Bool.not(sh(S, id)),
        and_true(Bool.not(has(t, id)), am1(t, id),
          b_not_f(has(t, id), b_nand2(has(t, id),
            sh(Cli.SeenArg{X, s, l} <> List.append(&2, Cli.Seen, al, S), id),
            and_right(am1(t, id), Bool.or(Bool.not(has(t, id)),
              Bool.not(sh(Cli.SeenArg{X, s, l} <> List.append(&2, Cli.Seen,
                al, S), id))), ih),
            b_or_l(String.eq(id, X), sh(List.append(&2, Cli.Seen, al, S), id),
              eq_flip(X, id, ec)))),
          and_left(am1(t, id), Bool.or(Bool.not(has(t, id)),
            Bool.not(sh(Cli.SeenArg{X, s, l} <> List.append(&2, Cli.Seen, al,
              S), id))), ih)),
        b_not_f(sh(S, id), sh_tr(S, X, id, ec, ns)))
    case False{}:
      and_true(am1(t, id), Bool.or(Bool.not(has(t, id)), Bool.not(sh(S, id))),
        and_left(am1(t, id), Bool.or(Bool.not(has(t, id)),
          Bool.not(sh(Cli.SeenArg{X, s, l} <> List.append(&2, Cli.Seen, al,
            S), id))), ih),
        qam_w(t, S, al, X, id, sal, and_right(am1(t, id),
          Bool.or(Bool.not(has(t, id)), Bool.not(sh(Cli.SeenArg{X, s, l}
            <> List.append(&2, Cli.Seen, al, S), id))), ih)))

def qam_arg(parsed: Cli.Usage, +usage: String, -help: String,
    +attrs: List<&2, Cli.Item>, +t: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String,
    +a: {argq(parsed, attrs, S) == True{} : Bool},
    ih: {Bool.and(am1(t, id), Bool.or(Bool.not(has(t, id)),
      Bool.not(sh(List.append(&2, Cli.Seen, Cli.arg_entries(parsed, attrs),
        S), id)))) == True{} : Bool}) ->
    {Bool.and(Bool.and(Bool.or(Bool.not(String.eq(Cli.info_id(
      Cli.arg_info_parsed(parsed, usage, attrs)), id)), Bool.not(has(t, id))),
      am1(t, id)), Bool.or(Bool.not(Bool.or(String.eq(Cli.info_id(
        Cli.arg_info_parsed(parsed, usage, attrs)), id), has(t, id))),
      Bool.not(sh(S, id)))) == True{} : Bool}:
  match parsed:
    case Cli.Invalid{col}:
      Empty.absurd({Bool.and(Bool.and(Bool.or(Bool.not(String.eq("", id)),
        Bool.not(has(t, id))), am1(t, id)), Bool.or(Bool.not(Bool.or(
        String.eq("", id), has(t, id))), Bool.not(sh(S, id)))) == True{}
        : Bool}, false_true_absurd(a))
    case Cli.Parsed{+derived, +s, +l, k}:
      qam_c(String.eq(Cli.use_id(Cli.find_id(attrs), derived), id),
        Cli.use_id(Cli.find_id(attrs), derived), s, l, t, S,
        Cli.arg_alias_entries(Cli.find_aliases(attrs)), id, {==},
        nt_f(sh(S, Cli.use_id(Cli.find_id(attrs), derived)),
          and_left(Bool.not(sh(S, Cli.use_id(Cli.find_id(attrs), derived))),
            Bool.or(Bool.not(Cli.has_global(attrs)), Bool.not(Cli.kind_pos(k))),
            a)), ih, sh_alias(Cli.find_aliases(attrs), S, id))

def qam_sub(+t: List<&2, Cli.Item>, +al: List<&2, String>, +n: String,
    +S: List<&2, Cli.Seen>, +id: String,
    ih: {Bool.and(am1(t, id), Bool.or(Bool.not(has(t, id)),
      Bool.not(sh(List.append(&2, Cli.Seen, Cli.sub_alias_entries(al),
        Cli.SeenSub{n} <> S), id)))) == True{} : Bool}) ->
    {Bool.and(am1(t, id), Bool.or(Bool.not(has(t, id)), Bool.not(sh(S, id))))
      == True{} : Bool}:
  %sh_sub(al, n, S, id) : {Bool.and(am1(t, id), Bool.or(Bool.not(has(t, id)),
    Bool.not(_))) == True{} : Bool}
  ih

def qam(I: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, +id: String,
    +q: {qt(I, S, H) == True{} : Bool}) ->
    {Bool.and(am1(I, id), Bool.or(Bool.not(has(I, id)), Bool.not(sh(S, id))))
      == True{} : Bool}:
  match I:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      qam_arg(Cli.parse_usage(usage), usage, help, attrs, tail, S, id,
        and_left(argq(Cli.parse_usage(usage), attrs, S),
          qt(tail, List.append(&2, Cli.Seen, Cli.arg_entries(
            Cli.parse_usage(usage), attrs), S), H), q),
        qam(tail, List.append(&2, Cli.Seen, Cli.arg_entries(
          Cli.parse_usage(usage), attrs), S), H, id,
          and_right(argq(Cli.parse_usage(usage), attrs, S),
            qt(tail, List.append(&2, Cli.Seen, Cli.arg_entries(
              Cli.parse_usage(usage), attrs), S), H), q)))
    case Cli.Sub{+name, about, +children} <> +tail:
      qam_sub(tail, Cli.find_aliases(children), name, S, id,
        qam(tail, List.append(&2, Cli.Seen,
          Cli.sub_alias_entries(Cli.find_aliases(children)),
          Cli.SeenSub{name} <> S), H, id,
          and_right(qt(children, H, List.append(&2, Cli.Seen,
            Cli.global_entries(Cli.lint_items(children)), H)),
            qt(tail, List.append(&2, Cli.Seen,
              Cli.sub_alias_entries(Cli.find_aliases(children)),
              Cli.SeenSub{name} <> S), H),
            and_right(Bool.not(Cli.sub_collision(S, name)),
              Bool.and(qt(children, H, List.append(&2, Cli.Seen,
                Cli.global_entries(Cli.lint_items(children)), H)),
                qt(tail, List.append(&2, Cli.Seen,
                  Cli.sub_alias_entries(Cli.find_aliases(children)),
                  Cli.SeenSub{name} <> S), H)), q))))
    case Cli.Version{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Alias{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Hidden{} <> tail: qam(tail, S, H, id, q)
    case Cli.Example{x0, x1} <> tail: qam(tail, S, H, id, q)
    case Cli.After{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.SubOptional{} <> tail: qam(tail, S, H, id, q)
    case Cli.External{} <> tail: qam(tail, S, H, id, q)
    case Cli.Exclusive{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.NeedOne{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Id{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Required{} <> tail: qam(tail, S, H, id, q)
    case Cli.AttrDefault{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.AttrEnv{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Global{} <> tail: qam(tail, S, H, id, q)
    case Cli.Heading{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.As{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.OneOf{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Delim{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Hyphen{} <> tail: qam(tail, S, H, id, q)
    case Cli.Rest{} <> tail: qam(tail, S, H, id, q)
    case Cli.Bare{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Conflicts{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Requires{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Group{x0} <> tail: qam(tail, S, H, id, q)
    case Cli.Builtin{} <> tail: qam(tail, S, H, id, q)

def b3(e: Bool, h: Bool, s: Bool, sg: Bool,
    l1: {Bool.or(Bool.not(e), s) == True{} : Bool},
    ih: {Bool.or(Bool.not(h), sg) == True{} : Bool},
    up: {Bool.or(Bool.not(sg), s) == True{} : Bool}) ->
    {Bool.or(Bool.not(Bool.or(e, h)), s) == True{} : Bool}:
  match e:
    case True{}: l1
    case False{}:
      match h:
        case True{}: b_imp(sg, s, up, ih)
        case False{}: {==}

def ent_c(c: Bool, +X: String, -s: String, -l: String,
    -r: List<&2, Cli.Seen>, +id: String,
    ec: {String.eq(X, id) == c : Bool}) ->
    {Bool.or(Bool.not(c), sh(Cli.SeenArg{X, s, l} <> r, id)) == True{}
      : Bool}:
  match c:
    case True{}: b_or_l(String.eq(id, X), sh(r, id), eq_flip(X, id, ec))
    case False{}: {==}

def ent_sh(parsed: Cli.Usage, +usage: String, +attrs: List<&2, Cli.Item>,
    -S: List<&2, Cli.Seen>, +id: String, -rest: List<&2, Cli.Seen>,
    a: {argq(parsed, attrs, S) == True{} : Bool}) ->
    {Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info_parsed(parsed, usage,
      attrs)), id)), sh(List.append(&2, Cli.Seen, Cli.arg_entries(parsed,
      attrs), rest), id)) == True{} : Bool}:
  match parsed:
    case Cli.Invalid{col}:
      Empty.absurd({Bool.or(Bool.not(String.eq("", id)), sh(rest, id))
        == True{} : Bool}, false_true_absurd(a))
    case Cli.Parsed{+derived, +s, +l, k}:
      ent_c(String.eq(Cli.use_id(Cli.find_id(attrs), derived), id),
        Cli.use_id(Cli.find_id(attrs), derived), s, l,
        List.append(&2, Cli.Seen, Cli.arg_alias_entries(Cli.find_aliases(
          attrs)), rest), id, {==})

def gc_pick(g: Bool, +usage: String, -help: String,
    +attrs: List<&2, Cli.Item>, +gt: List<&2, Cli.Item>,
    +get: List<&2, Cli.Seen>, +id: String,
    l1: {Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)),
      id)), sh(List.append(&2, Cli.Seen, Cli.arg_entries(
      Cli.parse_usage(usage), attrs), get), id)) == True{} : Bool},
    ih: {Bool.or(Bool.not(has(gt, id)), sh(get, id)) == True{} : Bool},
    up: {Bool.or(Bool.not(sh(get, id)), sh(List.append(&2, Cli.Seen,
      Cli.arg_entries(Cli.parse_usage(usage), attrs), get), id)) == True{}
      : Bool}) ->
    {Bool.or(Bool.not(has(Bool.pick(List<&2, Cli.Item>, g,
      Cli.Arg{usage, help, attrs} <> gt, gt), id)),
      sh(List.append(&2, Cli.Seen, Bool.pick(List<&2, Cli.Seen>, g,
        Cli.arg_entries(Cli.parse_usage(usage), attrs), Nil{}), get), id))
      == True{} : Bool}:
  match g:
    case True{}:
      b3(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id), has(gt, id),
        sh(List.append(&2, Cli.Seen, Cli.arg_entries(Cli.parse_usage(usage),
          attrs), get), id), sh(get, id), l1, ih, up)
    case False{}: ih

def gcov_go(I: List<&2, Cli.Item>, +all: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, +id: String,
    +q: {qt(I, S, H) == True{} : Bool}) ->
    {Bool.or(Bool.not(has(Cli.global_go(I, all), id)),
      sh(Cli.global_entries(Cli.lint_items(I)), id)) == True{} : Bool}:
  match I:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      gc_pick(Cli.has_global(attrs), usage, help, attrs,
        Cli.global_go(tail, all), Cli.global_entries(Cli.lint_items(tail)), id,
        ent_sh(Cli.parse_usage(usage), usage, attrs, S, id,
          Cli.global_entries(Cli.lint_items(tail)),
          and_left(argq(Cli.parse_usage(usage), attrs, S),
            qt(tail, List.append(&2, Cli.Seen, Cli.arg_entries(
              Cli.parse_usage(usage), attrs), S), H), q)),
        gcov_go(tail, all, List.append(&2, Cli.Seen, Cli.arg_entries(
          Cli.parse_usage(usage), attrs), S), H, id,
          and_right(argq(Cli.parse_usage(usage), attrs, S),
            qt(tail, List.append(&2, Cli.Seen, Cli.arg_entries(
              Cli.parse_usage(usage), attrs), S), H), q)),
        sh_up(Cli.arg_entries(Cli.parse_usage(usage), attrs),
          Cli.global_entries(Cli.lint_items(tail)), id))
    case Cli.Sub{+name, about, +children} <> +tail:
      gcov_go(tail, all, List.append(&2, Cli.Seen,
        Cli.sub_alias_entries(Cli.find_aliases(children)),
        Cli.SeenSub{name} <> S), H, id,
        and_right(qt(children, H, List.append(&2, Cli.Seen,
          Cli.global_entries(Cli.lint_items(children)), H)),
          qt(tail, List.append(&2, Cli.Seen,
            Cli.sub_alias_entries(Cli.find_aliases(children)),
            Cli.SeenSub{name} <> S), H),
          and_right(Bool.not(Cli.sub_collision(S, name)),
            Bool.and(qt(children, H, List.append(&2, Cli.Seen,
              Cli.global_entries(Cli.lint_items(children)), H)),
              qt(tail, List.append(&2, Cli.Seen,
                Cli.sub_alias_entries(Cli.find_aliases(children)),
                Cli.SeenSub{name} <> S), H)), q)))
    case Cli.Version{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Alias{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Hidden{} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Example{x0, x1} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.After{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.SubOptional{} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.External{} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Exclusive{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {Bool.or(Bool.not(has(G, id)),
          sh(Cli.global_entries(Cli.lint_items(tail)), id)) == True{} : Bool},
        Cli.Exclusive{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        gcov_go(tail, all, S, H, id, q), gcov_go(tail, all, S, H, id, q))
    case Cli.NeedOne{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {Bool.or(Bool.not(has(G, id)),
          sh(Cli.global_entries(Cli.lint_items(tail)), id)) == True{} : Bool},
        Cli.NeedOne{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        gcov_go(tail, all, S, H, id, q), gcov_go(tail, all, S, H, id, q))
    case Cli.Id{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Required{} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.AttrDefault{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.AttrEnv{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Global{} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Heading{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.As{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.OneOf{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Delim{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Hyphen{} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Rest{} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Bare{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Conflicts{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Requires{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Group{x0} <> tail: gcov_go(tail, all, S, H, id, q)
    case Cli.Builtin{} <> tail: gcov_go(tail, all, S, H, id, q)

def gcov(+I: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, +id: String,
    +q: {qt(I, S, H) == True{} : Bool}) ->
    {Bool.or(Bool.not(has(Cli.global_items(I), id)),
      sh(Cli.global_entries(Cli.lint_items(I)), id)) == True{} : Bool}:
  gcov_go(I, I, S, H, id, q)

def gn_parsed(parsed: Cli.Usage, -usage: String, +attrs: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, a: {argq(parsed, attrs, S) == True{} : Bool}) ->
    {Bool.or(Bool.not(Cli.has_global(attrs)), Bool.not(Cli.kind_pos(
      Cli.info_kind(Cli.arg_info_parsed(parsed, usage, attrs))))) == True{}
      : Bool}:
  match parsed:
    case Cli.Invalid{col}:
      Empty.absurd({Bool.or(Bool.not(Cli.has_global(attrs)),
        Bool.not(Cli.kind_pos(Cli.FlagKind{}))) == True{} : Bool},
        false_true_absurd(a))
    case Cli.Parsed{derived, s, l, +k}:
      and_right(Bool.not(sh(S, Cli.use_id(Cli.find_id(attrs), derived))),
        Bool.or(Bool.not(Cli.has_global(attrs)), Bool.not(Cli.kind_pos(k))), a)

def gn_pick(g: Bool, +usage: String, -help: String, +attrs: List<&2, Cli.Item>,
    +gt: List<&2, Cli.Item>,
    l1: {Bool.or(Bool.not(g), Bool.not(Cli.kind_pos(Cli.info_kind(
      Cli.arg_info(usage, attrs))))) == True{} : Bool},
    ih: {nonpos(gt) == True{} : Bool}) ->
    {nonpos(Bool.pick(List<&2, Cli.Item>, g, Cli.Arg{usage, help, attrs} <> gt,
      gt)) == True{} : Bool}:
  match g:
    case True{}:
      and_true(Bool.not(Cli.kind_pos(Cli.info_kind(Cli.arg_info(usage,
        attrs)))), nonpos(gt), l1, ih)
    case False{}: ih

def gnonpos_go(I: List<&2, Cli.Item>, +all: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, +q: {qt(I, S, H) == True{} : Bool}) ->
    {nonpos(Cli.global_go(I, all)) == True{} : Bool}:
  match I:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      gn_pick(Cli.has_global(attrs), usage, help, attrs,
        Cli.global_go(tail, all),
        gn_parsed(Cli.parse_usage(usage), usage, attrs, S,
          and_left(argq(Cli.parse_usage(usage), attrs, S),
            qt(tail, List.append(&2, Cli.Seen, Cli.arg_entries(
              Cli.parse_usage(usage), attrs), S), H), q)),
        gnonpos_go(tail, all, List.append(&2, Cli.Seen, Cli.arg_entries(
          Cli.parse_usage(usage), attrs), S), H,
          and_right(argq(Cli.parse_usage(usage), attrs, S),
            qt(tail, List.append(&2, Cli.Seen, Cli.arg_entries(
              Cli.parse_usage(usage), attrs), S), H), q)))
    case Cli.Sub{+name, about, +children} <> +tail:
      gnonpos_go(tail, all, List.append(&2, Cli.Seen,
        Cli.sub_alias_entries(Cli.find_aliases(children)),
        Cli.SeenSub{name} <> S), H,
        and_right(qt(children, H, List.append(&2, Cli.Seen,
          Cli.global_entries(Cli.lint_items(children)), H)),
          qt(tail, List.append(&2, Cli.Seen,
            Cli.sub_alias_entries(Cli.find_aliases(children)),
            Cli.SeenSub{name} <> S), H),
          and_right(Bool.not(Cli.sub_collision(S, name)),
            Bool.and(qt(children, H, List.append(&2, Cli.Seen,
              Cli.global_entries(Cli.lint_items(children)), H)),
              qt(tail, List.append(&2, Cli.Seen,
                Cli.sub_alias_entries(Cli.find_aliases(children)),
                Cli.SeenSub{name} <> S), H)), q)))
    case Cli.Version{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Alias{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Hidden{} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Example{x0, x1} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.After{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.SubOptional{} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.External{} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Exclusive{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {nonpos(G) == True{} : Bool},
        Cli.Exclusive{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        gnonpos_go(tail, all, S, H, q), gnonpos_go(tail, all, S, H, q))
    case Cli.NeedOne{+x0} <> +tail:
      item_pick(Cli.group_global(all, x0),
        G => {nonpos(G) == True{} : Bool},
        Cli.NeedOne{x0} <> Cli.global_go(tail, all), Cli.global_go(tail, all),
        gnonpos_go(tail, all, S, H, q), gnonpos_go(tail, all, S, H, q))
    case Cli.Id{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Required{} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.AttrDefault{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.AttrEnv{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Global{} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Heading{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.As{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.OneOf{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Delim{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Hyphen{} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Rest{} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Bare{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Conflicts{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Requires{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Group{x0} <> tail: gnonpos_go(tail, all, S, H, q)
    case Cli.Builtin{} <> tail: gnonpos_go(tail, all, S, H, q)

def gnonpos(+I: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, +q: {qt(I, S, H) == True{} : Bool}) ->
    {nonpos(Cli.global_items(I)) == True{} : Bool}:
  gnonpos_go(I, I, S, H, q)

def sfn(o: Maybe<&2, Cli.SubFound>, +d: String) -> String:
  match o:
    case None{}: d
    case Some{Cli.SubFound{a, b}}: a

def sfc(o: Maybe<&2, Cli.SubFound>, +d: List<&2, Cli.Item>) ->
    List<&2, Cli.Item>:
  match o:
    case None{}: d
    case Some{Cli.SubFound{a, b}}: b

def sf_none_some(-h: Cli.SubFound,
    e: {None{} == Some{h} : Maybe<&2, Cli.SubFound>}) -> Empty:
  false_true_absurd(Equal.cong(Maybe<&2, Cli.SubFound>, Bool,
    m => Maybe.is_some(&2, Cli.SubFound, m), None{}, Some{h}, e))

def fsg_some(L: List<&2, Cli.Item>, -q: String, -h: Cli.SubFound) ->
    {Cli.find_sub_go(L, q, Some{h}) == Some{h} : Maybe<&2, Cli.SubFound>}:
  match L:
    case Nil{}: {==}
    case x <> t: {==}

def st_refl(+m: String) -> {Cli.same_text(m, m) == True{} : Bool}:
  Equal.trans(Bool, Cli.same_text(m, m), String.eq(m, m), True{},
    Laws.p18_text(m, m), string_eq_refl(m))

# The sub find_sub_go finds for a query: its own name finds it (from the
# start), seen has no sub of that name, and its children's tree holds.
def Canon(I: List<&2, Cli.Item>, n: String, ch: List<&2, Cli.Item>,
    S: List<&2, Cli.Seen>, H: List<&2, Cli.Seen>) -> Type:
  {Cli.find_sub_go(I, n, None{}) == Some{Cli.SubFound{n, ch}}
    : Maybe<&2, Cli.SubFound>} &
    ({Cli.sub_collision(S, n) == False{} : Bool} &
      {qt(ch, H, List.append(&2, Cli.Seen,
        Cli.global_entries(Cli.lint_items(ch)), H)) == True{} : Bool})

def hit_self(+m: String, -cm: List<&2, Cli.Item>, +t: List<&2, Cli.Item>) ->
    {Cli.find_sub_go(t, m, Cli.sub_hit(Cli.same_text(m, m), m, cm, m))
      == Some{Cli.SubFound{m, cm}} : Maybe<&2, Cli.SubFound>}:
  %Equal.sym(Bool, Cli.same_text(m, m), True{}, st_refl(m)) :
    {Cli.find_sub_go(t, m, Cli.sub_hit(_, m, cm, m))
      == Some{Cli.SubFound{m, cm}} : Maybe<&2, Cli.SubFound>}
  fsg_some(t, m, Cli.SubFound{m, cm})

def canon_hit(+m: String, -a: String, +cm: List<&2, Cli.Item>,
    +t: List<&2, Cli.Item>, -x: String, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, -n: String, -ch: List<&2, Cli.Item>,
    +q: {qt(Cli.Sub{m, a, cm} <> t, S, H) == True{} : Bool},
    ef: {Cli.find_sub_go(t, x, Some{Cli.SubFound{m, cm}})
      == Some{Cli.SubFound{n, ch}} : Maybe<&2, Cli.SubFound>}) ->
    Canon(Cli.Sub{m, a, cm} <> t, n, ch, S, H):
  +e0 = Equal.trans(Maybe<&2, Cli.SubFound>, Some{Cli.SubFound{m, cm}},
    Cli.find_sub_go(t, x, Some{Cli.SubFound{m, cm}}),
    Some{Cli.SubFound{n, ch}},
    Equal.sym(Maybe<&2, Cli.SubFound>,
      Cli.find_sub_go(t, x, Some{Cli.SubFound{m, cm}}),
      Some{Cli.SubFound{m, cm}}, fsg_some(t, x, Cli.SubFound{m, cm})), ef)
  %Equal.cong(Maybe<&2, Cli.SubFound>, String, o => sfn(o, m),
    Some{Cli.SubFound{m, cm}}, Some{Cli.SubFound{n, ch}}, e0) :
    Canon(Cli.Sub{m, a, cm} <> t, _, ch, S, H)
  %Equal.cong(Maybe<&2, Cli.SubFound>, List<&2, Cli.Item>, o => sfc(o, cm),
    Some{Cli.SubFound{m, cm}}, Some{Cli.SubFound{n, ch}}, e0) :
    Canon(Cli.Sub{m, a, cm} <> t, m, _, S, H)
  (hit_self(m, cm, t),
    (nt_f(Cli.sub_collision(S, m), and_left(Bool.not(Cli.sub_collision(S, m)),
      Bool.and(qt(cm, H, List.append(&2, Cli.Seen,
        Cli.global_entries(Cli.lint_items(cm)), H)),
        qt(t, List.append(&2, Cli.Seen,
          Cli.sub_alias_entries(Cli.find_aliases(cm)),
          Cli.SeenSub{m} <> S), H)), q)),
      and_left(qt(cm, H, List.append(&2, Cli.Seen,
        Cli.global_entries(Cli.lint_items(cm)), H)),
        qt(t, List.append(&2, Cli.Seen,
          Cli.sub_alias_entries(Cli.find_aliases(cm)),
          Cli.SeenSub{m} <> S), H),
        and_right(Bool.not(Cli.sub_collision(S, m)),
          Bool.and(qt(cm, H, List.append(&2, Cli.Seen,
            Cli.global_entries(Cli.lint_items(cm)), H)),
            qt(t, List.append(&2, Cli.Seen,
              Cli.sub_alias_entries(Cli.find_aliases(cm)),
              Cli.SeenSub{m} <> S), H)), q))))

def sc_sae(al: List<&2, String>, +R: List<&2, Cli.Seen>, +n: String,
    e: {Cli.sub_collision(List.append(&2, Cli.Seen,
      Cli.sub_alias_entries(al), R), n) == False{} : Bool}) ->
    {Cli.sub_collision(R, n) == False{} : Bool}:
  match al:
    case Nil{}: e
    case +a <> t:
      sc_sae(t, R, n, b_orf_r(Cli.same_text(n, a), Cli.sub_collision(
        List.append(&2, Cli.Seen, Cli.sub_alias_entries(t), R), n), e))

def text_flip_f(+a: String, +b: String,
    e: {Cli.same_text(a, b) == False{} : Bool}) ->
    {Cli.same_text(b, a) == False{} : Bool}:
  Equal.trans(Bool, Cli.same_text(b, a), String.eq(b, a), False{},
    Laws.p18_text(b, a), eq_flip_f(a, b, text_false(a, b, e)))

# No alias of cm collides with n: cm aliases n nowhere.
def sc_alias(cm: List<&2, Cli.Item>, +R: List<&2, Cli.Seen>, +n: String,
    +e: {Cli.sub_collision(List.append(&2, Cli.Seen,
      Cli.sub_alias_entries(Cli.find_aliases(cm)), R), n) == False{}
      : Bool}) -> {Cli.has_alias(cm, n, False{}) == False{} : Bool}:
  match cm:
    case Nil{}: {==}
    case Cli.Alias{+a} <> +tail:
      %Equal.sym(Bool, Cli.same_text(a, n), False{}, text_flip_f(n, a,
        b_orf_l(Cli.same_text(n, a), Cli.sub_collision(List.append(&2,
          Cli.Seen, Cli.sub_alias_entries(Cli.find_aliases(tail)), R), n), e))) :
        {Cli.has_alias(tail, n, _) == False{} : Bool}
      sc_alias(tail, R, n, b_orf_r(Cli.same_text(n, a), Cli.sub_collision(
        List.append(&2, Cli.Seen, Cli.sub_alias_entries(Cli.find_aliases(
          tail)), R), n), e))
    case Cli.Arg{x0, x1, x2} <> tail: sc_alias(tail, R, n, e)
    case Cli.Sub{x0, x1, x2} <> tail: sc_alias(tail, R, n, e)
    case Cli.Version{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Hidden{} <> tail: sc_alias(tail, R, n, e)
    case Cli.Example{x0, x1} <> tail: sc_alias(tail, R, n, e)
    case Cli.After{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.SubOptional{} <> tail: sc_alias(tail, R, n, e)
    case Cli.External{} <> tail: sc_alias(tail, R, n, e)
    case Cli.Exclusive{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.NeedOne{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Id{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Required{} <> tail: sc_alias(tail, R, n, e)
    case Cli.AttrDefault{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.AttrEnv{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Global{} <> tail: sc_alias(tail, R, n, e)
    case Cli.Heading{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.As{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.OneOf{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Delim{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Hyphen{} <> tail: sc_alias(tail, R, n, e)
    case Cli.Rest{} <> tail: sc_alias(tail, R, n, e)
    case Cli.Bare{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Conflicts{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Requires{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Group{x0} <> tail: sc_alias(tail, R, n, e)
    case Cli.Builtin{} <> tail: sc_alias(tail, R, n, e)

def miss_first(+m: String, +cm: List<&2, Cli.Item>, +t: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +n: String, -ch: List<&2, Cli.Item>,
    +e2: {Cli.sub_collision(List.append(&2, Cli.Seen,
      Cli.sub_alias_entries(Cli.find_aliases(cm)), Cli.SeenSub{m} <> S), n)
      == False{} : Bool},
    e1: {Cli.find_sub_go(t, n, None{}) == Some{Cli.SubFound{n, ch}}
      : Maybe<&2, Cli.SubFound>}) ->
    {Cli.find_sub_go(t, n, Cli.sub_hit(Cli.same_text(n, m), m, cm, n))
      == Some{Cli.SubFound{n, ch}} : Maybe<&2, Cli.SubFound>}:
  %Equal.sym(Bool, Cli.same_text(n, m), False{}, b_orf_l(Cli.same_text(n, m),
    Cli.sub_collision(S, n), sc_sae(Cli.find_aliases(cm), Cli.SeenSub{m} <> S,
      n, e2))) :
    {Cli.find_sub_go(t, n, Cli.sub_hit(_, m, cm, n))
      == Some{Cli.SubFound{n, ch}} : Maybe<&2, Cli.SubFound>}
  %Equal.sym(Bool, Cli.has_alias(cm, n, False{}), False{},
    sc_alias(cm, Cli.SeenSub{m} <> S, n, e2)) :
    {Cli.find_sub_go(t, n, Cli.alias_hit(_, m, cm))
      == Some{Cli.SubFound{n, ch}} : Maybe<&2, Cli.SubFound>}
  e1

def canon_miss(+m: String, -a: String, +cm: List<&2, Cli.Item>,
    +t: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>, -H: List<&2, Cli.Seen>,
    +n: String, -ch: List<&2, Cli.Item>,
    ih: Canon(t, n, ch, List.append(&2, Cli.Seen,
      Cli.sub_alias_entries(Cli.find_aliases(cm)), Cli.SeenSub{m} <> S), H)) ->
    Canon(Cli.Sub{m, a, cm} <> t, n, ch, S, H):
  match ih:
    case (e1, (+e2, e3)):
      (miss_first(m, cm, t, S, n, ch, e2, e1),
        (b_orf_r(Cli.same_text(n, m), Cli.sub_collision(S, n),
          sc_sae(Cli.find_aliases(cm), Cli.SeenSub{m} <> S, n, e2)), e3))

def canon_alias(b: Bool, +m: String, -a: String, +cm: List<&2, Cli.Item>,
    +t: List<&2, Cli.Item>, -x: String, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, +n: String, -ch: List<&2, Cli.Item>,
    +q: {qt(Cli.Sub{m, a, cm} <> t, S, H) == True{} : Bool},
    ef: {Cli.find_sub_go(t, x, Cli.alias_hit(b, m, cm))
      == Some{Cli.SubFound{n, ch}} : Maybe<&2, Cli.SubFound>},
    ih: {Cli.find_sub_go(t, x, None{}) == Some{Cli.SubFound{n, ch}}
      : Maybe<&2, Cli.SubFound>} -> Canon(t, n, ch, List.append(&2, Cli.Seen,
      Cli.sub_alias_entries(Cli.find_aliases(cm)), Cli.SeenSub{m} <> S), H)) ->
    Canon(Cli.Sub{m, a, cm} <> t, n, ch, S, H):
  match b:
    case True{}: canon_hit(m, a, cm, t, x, S, H, n, ch, q, ef)
    case False{}: canon_miss(m, a, cm, t, S, H, n, ch, ih(ef))

def canon_sub(b: Bool, +m: String, -a: String, +cm: List<&2, Cli.Item>,
    +t: List<&2, Cli.Item>, +x: String, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, +n: String, -ch: List<&2, Cli.Item>,
    +q: {qt(Cli.Sub{m, a, cm} <> t, S, H) == True{} : Bool},
    ef: {Cli.find_sub_go(t, x, Cli.sub_hit(b, m, cm, x))
      == Some{Cli.SubFound{n, ch}} : Maybe<&2, Cli.SubFound>},
    ih: {Cli.find_sub_go(t, x, None{}) == Some{Cli.SubFound{n, ch}}
      : Maybe<&2, Cli.SubFound>} -> Canon(t, n, ch, List.append(&2, Cli.Seen,
      Cli.sub_alias_entries(Cli.find_aliases(cm)), Cli.SeenSub{m} <> S), H)) ->
    Canon(Cli.Sub{m, a, cm} <> t, n, ch, S, H):
  match b:
    case True{}: canon_hit(m, a, cm, t, x, S, H, n, ch, q, ef)
    case False{}:
      canon_alias(Cli.has_alias(cm, x, False{}), m, a, cm, t, x, S, H, n, ch,
        q, ef, ih)

def sc_arg_alias(xs: List<&2, String>, +S: List<&2, Cli.Seen>, +n: String) ->
    {Cli.sub_collision(List.append(&2, Cli.Seen, Cli.arg_alias_entries(xs), S),
      n) == Cli.sub_collision(S, n) : Bool}:
  match xs:
    case Nil{}: {==}
    case a <> t: sc_arg_alias(t, S, n)

def sc_args(parsed: Cli.Usage, +attrs: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +n: String) ->
    {Cli.sub_collision(List.append(&2, Cli.Seen, Cli.arg_entries(parsed,
      attrs), S), n) == Cli.sub_collision(S, n) : Bool}:
  match parsed:
    case Cli.Invalid{col}: {==}
    case Cli.Parsed{d, s, l, k}: sc_arg_alias(Cli.find_aliases(attrs), S, n)

def sc_arg_tr(parsed: Cli.Usage, +attrs: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +n: String,
    e: {Cli.sub_collision(List.append(&2, Cli.Seen, Cli.arg_entries(parsed,
      attrs), S), n) == False{} : Bool}) ->
    {Cli.sub_collision(S, n) == False{} : Bool}:
  %sc_args(parsed, attrs, S, n) : {_ == False{} : Bool}
  e

# The sub a query finds in a linted scope (canon).

def canon_arg(parsed: Cli.Usage, +attrs: List<&2, Cli.Item>,
    -t: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>, -H: List<&2, Cli.Seen>,
    +n: String, -ch: List<&2, Cli.Item>,
    ih: Canon(t, n, ch, List.append(&2, Cli.Seen,
      Cli.arg_entries(parsed, attrs), S), H)) -> Canon(t, n, ch, S, H):
  match ih:
    case (e1, (e2, e3)):
      (e1, (sc_arg_tr(parsed, attrs, S, n, e2), e3))

def canon(I: List<&2, Cli.Item>, +x: String, +S: List<&2, Cli.Seen>,
    +H: List<&2, Cli.Seen>, +n: String, -ch: List<&2, Cli.Item>,
    +q: {qt(I, S, H) == True{} : Bool},
    ef: {Cli.find_sub_go(I, x, None{}) == Some{Cli.SubFound{n, ch}}
      : Maybe<&2, Cli.SubFound>}) -> Canon(I, n, ch, S, H):
  match I:
    case Nil{}:
      Empty.absurd(Canon(Nil{}, n, ch, S, H),
        sf_none_some(Cli.SubFound{n, ch}, ef))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      canon_arg(Cli.parse_usage(usage), attrs, tail, S, H, n, ch,
        canon(tail, x, List.append(&2, Cli.Seen, Cli.arg_entries(
          Cli.parse_usage(usage), attrs), S), H, n, ch,
          and_right(argq(Cli.parse_usage(usage), attrs, S),
            qt(tail, List.append(&2, Cli.Seen, Cli.arg_entries(
              Cli.parse_usage(usage), attrs), S), H), q), ef))
    case Cli.Sub{+name, about, +children} <> +tail:
      canon_sub(Cli.same_text(x, name), name, about, children, tail, x, S, H,
        n, ch, q, ef,
        et => canon(tail, x, List.append(&2, Cli.Seen,
          Cli.sub_alias_entries(Cli.find_aliases(children)),
          Cli.SeenSub{name} <> S), H, n, ch,
          and_right(qt(children, H, List.append(&2, Cli.Seen,
            Cli.global_entries(Cli.lint_items(children)), H)),
            qt(tail, List.append(&2, Cli.Seen,
              Cli.sub_alias_entries(Cli.find_aliases(children)),
              Cli.SeenSub{name} <> S), H),
            and_right(Bool.not(Cli.sub_collision(S, name)),
              Bool.and(qt(children, H, List.append(&2, Cli.Seen,
                Cli.global_entries(Cli.lint_items(children)), H)),
                qt(tail, List.append(&2, Cli.Seen,
                  Cli.sub_alias_entries(Cli.find_aliases(children)),
                  Cli.SeenSub{name} <> S), H)), q)), et))
    case Cli.Version{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Alias{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Hidden{} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Example{x0, x1} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.After{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.SubOptional{} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.External{} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Exclusive{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.NeedOne{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Id{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Required{} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.AttrDefault{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.AttrEnv{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Global{} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Heading{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.As{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.OneOf{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Delim{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Hyphen{} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Rest{} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Bare{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Conflicts{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Requires{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Group{x0} <> tail: canon(tail, x, S, H, n, ch, q, ef)
    case Cli.Builtin{} <> tail: canon(tail, x, S, H, n, ch, q, ef)

# P21 hits: the arg a scope's option lookup finds is the one arg_ref finds
# for its id, so every arg of that id accepts the hit it makes.

def ofound_arg(m: Maybe<&2, Cli.OptFound>, +d: Cli.ArgInfo) -> Cli.ArgInfo:
  match m:
    case None{}: d
    case Some{Cli.OptFound{a, p}}: a

def of_none_some(-h: Cli.OptFound,
    e: {None{} == Some{h} : Maybe<&2, Cli.OptFound>}) -> Empty:
  false_true_absurd(Equal.cong(Maybe<&2, Cli.OptFound>, Bool,
    m => Maybe.is_some(&2, Cli.OptFound, m), None{}, Some{h}, e))

def om_pick(b: Bool, -info: Cli.ArgInfo, -neg: Bool, -x: Cli.ArgInfo,
    -pol: Bool,
    e: {Bool.pick(Maybe<&2, Cli.OptFound>, b, Some{Cli.OptFound{info, neg}},
      None{}) == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>}) ->
    {info == x : Cli.ArgInfo}:
  match b:
    case True{}:
      Equal.cong(Maybe<&2, Cli.OptFound>, Cli.ArgInfo, m => ofound_arg(m, x),
        Some{Cli.OptFound{info, neg}}, Some{Cli.OptFound{x, pol}}, e)
    case False{}:
      Empty.absurd({info == x : Cli.ArgInfo},
        of_none_some(Cli.OptFound{x, pol}, e))

# The arg option_matches answers with is the one it was given.
def om_info(+q: String, info: Cli.ArgInfo, -x: Cli.ArgInfo, -pol: Bool,
    e: {Cli.option_matches(q, info) == Some{Cli.OptFound{x, pol}}
      : Maybe<&2, Cli.OptFound>}) -> {info == x : Cli.ArgInfo}:
  match info:
    case Cli.ArgInfo{id, usage, +short, +long, +kind, +attrs}:
      om_pick(Bool.or(
        Bool.or(Bool.and(Bool.not(String.is_empty(short)),
          String.eq(q, short)),
          Bool.or(Bool.and(Bool.not(String.is_empty(long)),
            String.eq(q, long)),
            List.contains(~String, ~String.eq, Cli.find_aliases(attrs), q))),
        Bool.and(Cli.kind_negatable(kind),
          Bool.and(Bool.not(String.is_empty(long)),
            String.eq(q, Cli.negated_long(long))))),
        Cli.ArgInfo{id, usage, short, long, kind, attrs},
        Bool.not(Bool.and(Cli.kind_negatable(kind),
          Bool.and(Bool.not(String.is_empty(long)),
            String.eq(q, Cli.negated_long(long))))), x, pol, e)

def fo_none(c: Bool, -info: Cli.ArgInfo, +tail: List<&2, Cli.Item>,
    +id: String, -x: Cli.ArgInfo,
    hn: {Bool.or(Bool.not(c), Bool.not(has(tail, id))) == True{} : Bool},
    ih: {Laws.arg_ref(tail, id) == Some{x} : Maybe<&2, Cli.ArgInfo>}) ->
    {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info}, Laws.arg_ref(tail, id))
      == Some{x} : Maybe<&2, Cli.ArgInfo>}:
  match c:
    case True{}:
      Empty.absurd({Some{info} == Some{x} : Maybe<&2, Cli.ArgInfo>},
        true_false_absurd(Equal.trans(Bool, True{}, has(tail, id), False{},
          Equal.sym(Bool, has(tail, id), True{}, ref_found(tail, id, x, ih)),
          nt_f(has(tail, id), hn))))
    case False{}: ih

def fo_pick(m: Maybe<&2, Cli.OptFound>, +info: Cli.ArgInfo,
    +tail: List<&2, Cli.Item>, +q: String, -x: Cli.ArgInfo, -pol: Bool,
    +id: String,
    em: {Cli.option_matches(q, info) == m : Maybe<&2, Cli.OptFound>},
    ef: {Bool.pick(Maybe<&2, Cli.OptFound>,
      Maybe.is_some(&2, Cli.OptFound, m), m, Cli.find_option(tail, q))
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    hn: {Bool.or(Bool.not(String.eq(Cli.info_id(info), id)),
      Bool.not(has(tail, id))) == True{} : Bool},
    eid: {String.eq(Cli.info_id(x), id) == True{} : Bool},
    ih: {Cli.find_option(tail, q) == Some{Cli.OptFound{x, pol}}
      : Maybe<&2, Cli.OptFound>} ->
      {Laws.arg_ref(tail, id) == Some{x} : Maybe<&2, Cli.ArgInfo>}) ->
    {Bool.pick(Maybe<&2, Cli.ArgInfo>, String.eq(Cli.info_id(info), id),
      Some{info}, Laws.arg_ref(tail, id)) == Some{x}
      : Maybe<&2, Cli.ArgInfo>}:
  match m:
    case Some{f}:
      %Equal.sym(Cli.ArgInfo, info, x, om_info(q, info, x, pol,
        Equal.trans(Maybe<&2, Cli.OptFound>, Cli.option_matches(q, info),
          Some{f}, Some{Cli.OptFound{x, pol}}, em, ef))) :
        {Bool.pick(Maybe<&2, Cli.ArgInfo>, String.eq(Cli.info_id(_), id),
          Some{_}, Laws.arg_ref(tail, id)) == Some{x}
          : Maybe<&2, Cli.ArgInfo>}
      %Equal.sym(Bool, String.eq(Cli.info_id(x), id), True{}, eid) :
        {Bool.pick(Maybe<&2, Cli.ArgInfo>, _, Some{x},
          Laws.arg_ref(tail, id)) == Some{x} : Maybe<&2, Cli.ArgInfo>}
      {==}
    case None{}:
      fo_none(String.eq(Cli.info_id(info), id), info, tail, id, x, hn, ih(ef))

# The arg of id find_option finds is the one arg_ref finds, when at most one
# arg has id.
def fo_ref(L: List<&2, Cli.Item>, +q: String, -x: Cli.ArgInfo, -pol: Bool,
    +id: String,
    ef: {Cli.find_option(L, q) == Some{Cli.OptFound{x, pol}}
      : Maybe<&2, Cli.OptFound>},
    +am: {am1(L, id) == True{} : Bool},
    +eid: {String.eq(Cli.info_id(x), id) == True{} : Bool}) ->
    {Laws.arg_ref(L, id) == Some{x} : Maybe<&2, Cli.ArgInfo>}:
  match L:
    case Nil{}:
      Empty.absurd({Laws.arg_ref(Nil{}, id) == Some{x}
        : Maybe<&2, Cli.ArgInfo>}, of_none_some(Cli.OptFound{x, pol}, ef))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      fo_pick(Cli.option_matches(q, Cli.arg_info(usage, attrs)),
        Cli.arg_info(usage, attrs), tail, q, x, pol, id, {==}, ef,
        and_left(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(usage,
          attrs)), id)), Bool.not(has(tail, id))), am1(tail, id), am), eid,
        et => fo_ref(tail, q, x, pol, id, et,
          and_right(Bool.or(Bool.not(String.eq(Cli.info_id(
            Cli.arg_info(usage, attrs)), id)), Bool.not(has(tail, id))),
            am1(tail, id), am), eid))
    case Cli.Sub{x0, x1, x2} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Version{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Alias{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Hidden{} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Example{x0, x1} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.After{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.SubOptional{} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.External{} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Exclusive{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.NeedOne{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Id{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Required{} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.AttrDefault{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.AttrEnv{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Global{} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Heading{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.As{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.OneOf{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Delim{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Hyphen{} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Rest{} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Bare{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Conflicts{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Requires{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Group{x0} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)
    case Cli.Builtin{} <> tail: fo_ref(tail, q, x, pol, id, ef, am, eid)

def ok_conv(+e: Cli.ScanEvent, +id: String, -a: Cli.ArgInfo,
    -b: Cli.ArgInfo, eab: {a == b : Cli.ArgInfo},
    ok: {ev_ok(e, Cli.info_kind(a), Cli.info_attrs(a), id) == True{} : Bool})
    -> {ev_ok(e, Cli.info_kind(b), Cli.info_attrs(b), id) == True{} : Bool}:
  %eab : {ev_ok(e, Cli.info_kind(_), Cli.info_attrs(_), id) == True{} : Bool}
  ok

def acc_one_pick(c: Bool, +info: Cli.ArgInfo, +tail: List<&2, Cli.Item>,
    +e: Cli.ScanEvent, +id: String, -r: Cli.ArgInfo,
    am: {Bool.and(Bool.or(Bool.not(c), Bool.not(has(tail, id))),
      am1(tail, id)) == True{} : Bool},
    er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info},
      Laws.arg_ref(tail, id)) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    ok: {ev_ok(e, Cli.info_kind(r), Cli.info_attrs(r), id) == True{} : Bool},
    ih: {am1(tail, id) == True{} : Bool} ->
      {Laws.arg_ref(tail, id) == Some{r} : Maybe<&2, Cli.ArgInfo>} ->
      {acc(tail, e, id) == True{} : Bool}) ->
    {Bool.and(Bool.or(Bool.not(c), ev_ok(e, Cli.info_kind(info),
      Cli.info_attrs(info), id)), acc(tail, e, id)) == True{} : Bool}:
  match c:
    case True{}:
      and_true(ev_ok(e, Cli.info_kind(info), Cli.info_attrs(info), id),
        acc(tail, e, id),
        ok_conv(e, id, r, info, Equal.sym(Cli.ArgInfo, info, r,
          some_inj(info, r, er)), ok),
        acc_none(tail, e, id, nt_f(has(tail, id),
          and_left(Bool.not(has(tail, id)), am1(tail, id), am))))
    case False{}: ih(am, er)

# The one arg of id, which arg_ref finds, accepting e: all of L accepts e.
def acc_one(L: List<&2, Cli.Item>, +e: Cli.ScanEvent, +id: String,
    -r: Cli.ArgInfo, +am: {am1(L, id) == True{} : Bool},
    er: {Laws.arg_ref(L, id) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    +ok: {ev_ok(e, Cli.info_kind(r), Cli.info_attrs(r), id) == True{}
      : Bool}) -> {acc(L, e, id) == True{} : Bool}:
  match L:
    case Nil{}:
      Empty.absurd({acc(Nil{}, e, id) == True{} : Bool},
        arg_none_some(r, er))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      acc_one_pick(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), tail, e, id, r, am, er, ok,
        ea => et => acc_one(tail, e, id, r, ea, et, ok))
    case Cli.Sub{x0, x1, x2} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Version{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Alias{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Hidden{} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Example{x0, x1} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.After{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.SubOptional{} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.External{} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Exclusive{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.NeedOne{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Id{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Required{} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.AttrDefault{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.AttrEnv{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Global{} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Heading{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.As{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.OneOf{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Delim{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Hyphen{} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Rest{} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Bare{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Conflicts{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Requires{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Group{x0} <> tail: acc_one(tail, e, id, r, am, er, ok)
    case Cli.Builtin{} <> tail: acc_one(tail, e, id, r, am, er, ok)

# What a scope's ghost lists hold: the items' lint tree, the seen ids
# covering the inherited globals, which hold one arg of id at most and no
# positional.
def B0(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String) -> Bool:
  Bool.and(qt(I, S, List.append(&2, Cli.Seen,
    Cli.global_entries(Cli.lint_items(I)), S)),
    Bool.and(Bool.or(Bool.not(has(G, id)), sh(S, id)),
      Bool.and(am1(G, id), nonpos(G))))

def b0_qt(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String,
    b: {B0(I, G, S, id) == True{} : Bool}) ->
    {qt(I, S, List.append(&2, Cli.Seen,
      Cli.global_entries(Cli.lint_items(I)), S)) == True{} : Bool}:
  and_left(qt(I, S, List.append(&2, Cli.Seen,
    Cli.global_entries(Cli.lint_items(I)), S)),
    Bool.and(Bool.or(Bool.not(has(G, id)), sh(S, id)),
      Bool.and(am1(G, id), nonpos(G))), b)

def b0_rest(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String,
    b: {B0(I, G, S, id) == True{} : Bool}) ->
    {Bool.and(Bool.or(Bool.not(has(G, id)), sh(S, id)),
      Bool.and(am1(G, id), nonpos(G))) == True{} : Bool}:
  and_right(qt(I, S, List.append(&2, Cli.Seen,
    Cli.global_entries(Cli.lint_items(I)), S)),
    Bool.and(Bool.or(Bool.not(has(G, id)), sh(S, id)),
      Bool.and(am1(G, id), nonpos(G))), b)

def b0_cov(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String,
    b: {B0(I, G, S, id) == True{} : Bool}) ->
    {Bool.or(Bool.not(has(G, id)), sh(S, id)) == True{} : Bool}:
  and_left(Bool.or(Bool.not(has(G, id)), sh(S, id)),
    Bool.and(am1(G, id), nonpos(G)), b0_rest(I, G, S, id, b))

def b0_am(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String,
    b: {B0(I, G, S, id) == True{} : Bool}) ->
    {am1(G, id) == True{} : Bool}:
  and_left(am1(G, id), nonpos(G),
    and_right(Bool.or(Bool.not(has(G, id)), sh(S, id)),
      Bool.and(am1(G, id), nonpos(G)), b0_rest(I, G, S, id, b)))

def b0_np(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String,
    b: {B0(I, G, S, id) == True{} : Bool}) ->
    {nonpos(G) == True{} : Bool}:
  and_right(am1(G, id), nonpos(G),
    and_right(Bool.or(Bool.not(has(G, id)), sh(S, id)),
      Bool.and(am1(G, id), nonpos(G)), b0_rest(I, G, S, id, b)))

# qam on the items' tree: at most one arg of id, and none when seen has one.
def b0_qam(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String,
    b: {B0(I, G, S, id) == True{} : Bool}) ->
    {Bool.and(am1(I, id), Bool.or(Bool.not(has(I, id)), Bool.not(sh(S, id))))
      == True{} : Bool}:
  qam(I, S, List.append(&2, Cli.Seen,
    Cli.global_entries(Cli.lint_items(I)), S), id, b0_qt(I, G, S, id, b))

def hit_some(m: Maybe<&2, Cli.OptFound>, +I: List<&2, Cli.Item>,
    +G: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>, +q: String,
    -x: Cli.ArgInfo, -pol: Bool, +e: Cli.ScanEvent, +id: String,
    em: {Cli.find_option(I, q) == m : Maybe<&2, Cli.OptFound>},
    ef: {Maybe.or(&2, Cli.OptFound, m, Cli.find_option(G, q))
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    +ec: {String.eq(Cli.info_id(x), id) == True{} : Bool},
    +amI: {am1(I, id) == True{} : Bool},
    +dis: {Bool.or(Bool.not(has(I, id)), Bool.not(sh(S, id))) == True{}
      : Bool},
    +amG: {am1(G, id) == True{} : Bool},
    +cov: {Bool.or(Bool.not(has(G, id)), sh(S, id)) == True{} : Bool},
    +ok: {ev_ok(e, Cli.info_kind(x), Cli.info_attrs(x), id) == True{}
      : Bool}) ->
    ({acc(G, e, id) == True{} : Bool} & {acc(I, e, id) == True{} : Bool}):
  match m:
    case Some{f}:
      +rI = fo_ref(I, q, x, pol, id, Equal.trans(Maybe<&2, Cli.OptFound>,
        Cli.find_option(I, q), Some{f}, Some{Cli.OptFound{x, pol}}, em, ef),
        amI, ec)
      (acc_none(G, e, id, b_ornot(has(G, id), sh(S, id), cov,
        b_nand(has(I, id), sh(S, id), dis, ref_found(I, id, x, rI)))),
        acc_one(I, e, id, x, amI, rI, ok))
    case None{}:
      +rG = fo_ref(G, q, x, pol, id, ef, amG, ec)
      (acc_one(G, e, id, x, amG, rG, ok),
        acc_none(I, e, id, b_nand2(has(I, id), sh(S, id), dis,
          b_imp(has(G, id), sh(S, id), cov, ref_found(G, id, x, rG)))))

def hit_c(c: Bool, +I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +q: String, -x: Cli.ArgInfo, -pol: Bool,
    +e: Cli.ScanEvent, +id: String,
    ec: {String.eq(Cli.info_id(x), id) == c : Bool},
    ef: {Maybe.or(&2, Cli.OptFound, Cli.find_option(I, q),
      Cli.find_option(G, q)) == Some{Cli.OptFound{x, pol}}
      : Maybe<&2, Cli.OptFound>},
    +b: {B0(I, G, S, id) == True{} : Bool},
    ok: {ev_ok(e, Cli.info_kind(x), Cli.info_attrs(x), id) == True{} : Bool},
    +eo: {off(e, id) == Bool.not(c) : Bool}) ->
    ({acc(G, e, id) == True{} : Bool} & {acc(I, e, id) == True{} : Bool}):
  match c:
    case True{}:
      +qa = b0_qam(I, G, S, id, b)
      hit_some(Cli.find_option(I, q), I, G, S, q, x, pol, e, id, {==}, ef, ec,
        and_left(am1(I, id), Bool.or(Bool.not(has(I, id)),
          Bool.not(sh(S, id))), qa),
        and_right(am1(I, id), Bool.or(Bool.not(has(I, id)),
          Bool.not(sh(S, id))), qa),
        b0_am(I, G, S, id, b), b0_cov(I, G, S, id, b), ok)
    case False{}: (acc_off(G, e, id, eo), acc_off(I, e, id, eo))

# A hit for an arg the scope's lookup finds, which that arg accepts and
# which is off id unless that arg's id is id, every arg of the scope's
# ghost lists accepts.
def scope_hit(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +p: List<&2, String>, +q: String,
    x: Cli.ArgInfo, -pol: Bool, +e: Cli.ScanEvent, +id: String,
    +b: {B0(I, G, S, id) == True{} : Bool},
    ef: {Cli.find_option_scope(Cli.Scope{p,
      Cli.spec_node(I, Cli.spec_items(G))}, q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    ok: {ev_ok(e, Cli.info_kind(x), Cli.info_attrs(x), id) == True{} : Bool},
    eo: {off(e, id) == Bool.not(String.eq(Cli.info_id(x), id)) : Bool}) ->
    ({acc(G, e, id) == True{} : Bool} & {acc(I, e, id) == True{} : Bool}):
  hit_c(String.eq(Cli.info_id(x), id), I, G, S, q, x, pol, e, id, {==},
    Equal.trans(Maybe<&2, Cli.OptFound>,
      Maybe.or(&2, Cli.OptFound, Cli.find_option(I, q),
        Cli.find_option(G, q)),
      Cli.find_option_scope(Cli.Scope{p,
        Cli.spec_node(I, Cli.spec_items(G))}, q),
      Some{Cli.OptFound{x, pol}},
      Equal.sym(Maybe<&2, Cli.OptFound>,
        Cli.find_option_scope(Cli.Scope{p,
          Cli.spec_node(I, Cli.spec_items(G))}, q),
        Maybe.or(&2, Cli.OptFound, Cli.find_option(I, q),
          Cli.find_option(G, q)), Laws.p19_option(I, G, p, q)), ef),
    b, ok, eo)

# P21 scan: each mode the scan reaches keeps its scope at a path of the
# command's tree, with the ghost lists of that scope's own args (I) and the
# globals it inherits (G), the ids lint saw above it (S), and every event
# accepted by every arg of I and G with the law's id.

# The own items (hi) and inherited globals (hg) at a path, as scope_args
# walks them.
def hi(p: List<&2, String>, I: List<&2, Cli.Item>) -> List<&2, Cli.Item>:
  match p:
    case Nil{}: I
    case n <> t: hi(t, Cli.sub_items(Cli.find_sub(I, n)))

def hg(p: List<&2, String>, +I: List<&2, Cli.Item>,
    G: List<&2, Cli.Item>) -> List<&2, Cli.Item>:
  match p:
    case Nil{}: G
    case n <> t:
      hg(t, Cli.sub_items(Cli.find_sub(I, n)),
        List.append(&2, Cli.Item, Cli.global_items(I), G))

def hi_snoc(p: List<&2, String>, -n: String, -I: List<&2, Cli.Item>) ->
    {hi(List.append(&2, String, p, [n]), I)
      == Cli.sub_items(Cli.find_sub(hi(p, I), n)) : List<&2, Cli.Item>}:
  match p:
    case Nil{}: {==}
    case m <> t: hi_snoc(t, n, Cli.sub_items(Cli.find_sub(I, m)))

def hg_snoc(p: List<&2, String>, -n: String, -I: List<&2, Cli.Item>,
    -G: List<&2, Cli.Item>) ->
    {hg(List.append(&2, String, p, [n]), I, G)
      == List.append(&2, Cli.Item, Cli.global_items(hi(p, I)), hg(p, I, G))
      : List<&2, Cli.Item>}:
  match p:
    case Nil{}: {==}
    case m <> t:
      hg_snoc(t, n, Cli.sub_items(Cli.find_sub(I, m)),
        List.append(&2, Cli.Item, Cli.global_items(I), G))

def sa_hg(p: List<&2, String>, -I: List<&2, Cli.Item>,
    -G: List<&2, Cli.Item>) ->
    {Cli.scope_args(p, I, G) == List.append(&2, Cli.Item, hg(p, I, G),
      hi(p, I)) : List<&2, Cli.Item>}:
  match p:
    case Nil{}: {==}
    case n <> t:
      sa_hg(t, Cli.sub_items(Cli.find_sub(I, n)),
        List.append(&2, Cli.Item, Cli.global_items(I), G))

# What a scope and its events keep, at some path p of items0.
def ScInv(scope: Cli.Scope, events: List<&2, Cli.ScanEvent>,
    items0: List<&2, Cli.Item>, id: String) -> Type:
  &p: List<&2, String> -> &I: List<&2, Cli.Item> ->
  &G: List<&2, Cli.Item> -> &S: List<&2, Cli.Seen> ->
  ({scope == Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))} : Cli.Scope} &
   ({hi(p, items0) == I : List<&2, Cli.Item>} &
    ({hg(p, items0, Nil{}) == G : List<&2, Cli.Item>} &
     ({B0(I, G, S, id) == True{} : Bool} &
      ({ev_all(events, G, id) == True{} : Bool} &
       {ev_all(events, I, id) == True{} : Bool})))))

def SInv(st: Cli.ScanState, items0: List<&2, Cli.Item>, id: String) -> Type:
  match st:
    case Cli.ScanState{scope, events, resting, count, external, issue}:
      ScInv(scope, events, items0, id)

def TInv(t: Cli.Tail, items0: List<&2, Cli.Item>, id: String) -> Type:
  match t:
    case Cli.Faulted{st}: SInv(st, items0, id)
    case Cli.Walk{st}: SInv(st, items0, id)
    case Cli.Stopped{st}: SInv(st, items0, id)

# The option a Fetch waits on is one its scope finds, and takes a value.
def FInv(st: Cli.ScanState, info: Cli.ArgInfo) -> Type:
  &q: String -> &pol: Bool ->
  ({Cli.find_option_scope(Cli.scan_state_scope(st), q)
      == Some{Cli.OptFound{info, pol}} : Maybe<&2, Cli.OptFound>} &
   {Cli.kind_valued(Cli.info_kind(info)) == True{} : Bool})

def MInv(m: Cli.Mode, items0: List<&2, Cli.Item>, id: String) -> Type:
  match m:
    case Cli.Open{st}: SInv(st, items0, id)
    case Cli.Fetch{st, info}: SInv(st, items0, id) & FInv(st, info)
    case Cli.Operands{st, ended}: SInv(st, items0, id)
    case Cli.Capture{st, name}: SInv(st, items0, id)
    case Cli.Closed{t}: TInv(t, items0, id)

# An event off id keeps the invariant.
def push_off(state: Cli.ScanState, +e: Cli.ScanEvent,
    -items0: List<&2, Cli.Item>, +id: String,
    +eo: {off(e, id) == True{} : Bool}, inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_event(state, e), items0, id):
  match state:
    case Cli.ScanState{scope, +events, resting, count, external, issue}:
      match inv:
        case (p, (+I, (+G, (S, (es, (ei, (eg, (b, (eG, eI))))))))):
          (p, (I, (G, (S, (es, (ei, (eg, (b,
            (and_true(acc(G, e, id), ev_all(events, G, id),
              acc_off(G, e, id, eo), eG),
             and_true(acc(I, e, id), ev_all(events, I, id),
              acc_off(I, e, id, eo), eI))))))))))

def err_inv(state: Cli.ScanState, -fault: Cli.ScanFault,
    -items0: List<&2, Cli.Item>, -id: String, inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_error(state, fault), items0, id):
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}: inv

def ext_inv(state: Cli.ScanState, -name: String, -args: List<&2, String>,
    -items0: List<&2, Cli.Item>, -id: String, inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_external(state, name, args), items0, id):
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}: inv

def settle_case(resting: Bool, issue: Maybe<&2, Cli.ScanFault>,
    -scope: Cli.Scope, -events: List<&2, Cli.ScanEvent>, -count: Nat,
    -external: Maybe<&2, Cli.ExternalArgs>, -items0: List<&2, Cli.Item>,
    -id: String, inv: ScInv(scope, events, items0, id)) ->
    MInv(Cli.scan_settle_case(resting, issue, scope, events, count,
      external), items0, id):
  match resting:
    case True{}:
      match issue:
        case None{}: inv
        case Some{f}: inv
    case False{}:
      match issue:
        case None{}: inv
        case Some{f}: inv

def settle_inv(state: Cli.ScanState, -items0: List<&2, Cli.Item>,
    -id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_settle(state), items0, id):
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}:
      settle_case(resting, issue, scope, events, count, external, items0, id,
        inv)

def push_acc(-scope: Cli.Scope, +events: List<&2, Cli.ScanEvent>,
    -items0: List<&2, Cli.Item>, p: List<&2, String>, +I: List<&2, Cli.Item>,
    +G: List<&2, Cli.Item>, S: List<&2, Cli.Seen>, +e: Cli.ScanEvent,
    +id: String,
    h: ({acc(G, e, id) == True{} : Bool} & {acc(I, e, id) == True{} : Bool}),
    es: {scope == Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))}
      : Cli.Scope},
    ei: {hi(p, items0) == I : List<&2, Cli.Item>},
    eg: {hg(p, items0, Nil{}) == G : List<&2, Cli.Item>},
    b: {B0(I, G, S, id) == True{} : Bool},
    eG: {ev_all(events, G, id) == True{} : Bool},
    eI: {ev_all(events, I, id) == True{} : Bool}) ->
    ScInv(scope, e <> events, items0, id):
  match h:
    case (aG, aI):
      (p, (I, (G, (S, (es, (ei, (eg, (b,
        (and_true(acc(G, e, id), ev_all(events, G, id), aG, eG),
         and_true(acc(I, e, id), ev_all(events, I, id), aI, eI))))))))))

# A hit for an arg the scope finds, which that arg accepts and which is off
# id unless that arg's id is id, keeps the invariant.
def push_hit(state: Cli.ScanState, +q: String, x: Cli.ArgInfo, -pol: Bool,
    +e: Cli.ScanEvent, -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    ok: {ev_ok(e, Cli.info_kind(x), Cli.info_attrs(x), id) == True{} : Bool},
    eo: {off(e, id) == Bool.not(String.eq(Cli.info_id(x), id)) : Bool},
    inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_event(state, e), items0, id):
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}:
      match inv:
        case (+p, (+I, (+G, (+S, (+es, (ei, (eg, (+b, (eG, eI))))))))):
          push_acc(scope, events, items0, p, I, G, S, e, id,
            scope_hit(I, G, S, p, q, x, pol, e, id, b,
              (%es : {Cli.find_option_scope(_, q)
                == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>}
              ef), ok, eo),
            es, ei, eg, b, eG, eI)

def vr_hit(x: Cli.ArgInfo, state: Cli.ScanState, +q: String, -pol: Bool,
    +v: String, -items0: List<&2, Cli.Item>, +id: String,
    eb: {Cli.value_bad(Cli.info_attrs(x), v) == None{} : Maybe<&2, Cli.Bad>},
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    kv: {Cli.kind_valued(Cli.info_kind(x)) == True{} : Bool},
    inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_value_result(None{}, state, x, v), items0, id):
  match x:
    case Cli.ArgInfo{+k, u, s, l, +kind, +a}:
      push_hit(state, q, Cli.ArgInfo{k, u, s, l, kind, a}, pol,
        Cli.ValueHit{k, v}, items0, id, ef,
        b_or_r(Bool.not(String.eq(k, id)), Bool.and(Cli.kind_valued(kind),
          no_bad(Cli.value_bad(a, v))), and_true(Cli.kind_valued(kind),
          no_bad(Cli.value_bad(a, v)), kv, nb_of(Cli.value_bad(a, v), eb))),
        {==}, inv)

def vr_inv(found: Maybe<&2, Cli.Bad>, state: Cli.ScanState, x: Cli.ArgInfo,
    +q: String, -pol: Bool, +v: String, -items0: List<&2, Cli.Item>,
    +id: String,
    eb: {Cli.value_bad(Cli.info_attrs(x), v) == found : Maybe<&2, Cli.Bad>},
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    kv: {Cli.kind_valued(Cli.info_kind(x)) == True{} : Bool},
    inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_value_result(found, state, x, v), items0, id):
  match found:
    case None{}: vr_hit(x, state, q, pol, v, items0, id, eb, ef, kv, inv)
    case Some{bd}:
      match bd:
        case Cli.Bad{bad, why}:
          err_inv(state, Cli.E04{Cli.arg_display(x), bad, why}, items0, id, inv)

# A value for an arg the scope finds, which takes a value, keeps the
# invariant.
def value_inv(state: Cli.ScanState, +q: String, +x: Cli.ArgInfo, -pol: Bool,
    +v: String, -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    kv: {Cli.kind_valued(Cli.info_kind(x)) == True{} : Bool},
    inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_value(state, x, v), items0, id):
  vr_inv(Cli.value_bad(Cli.info_attrs(x), v), state, x, q, pol, v, items0,
    id, {==}, ef, kv, inv)

def so_inv(attached: Maybe<&2, String>, +state: Cli.ScanState,
    +x: Cli.ArgInfo, -pol: Bool, +e: Cli.ScanEvent, +q: String,
    -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    ok: {ev_ok(e, Cli.info_kind(x), Cli.info_attrs(x), id) == True{} : Bool},
    eo: {off(e, id) == Bool.not(String.eq(Cli.info_id(x), id)) : Bool},
    eh: {Cli.scan_event(state, e) == Cli.scan_simple_hit(state, x, pol)
      : Cli.ScanState},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_simple_option(attached, state, x, pol), items0, id):
  match attached:
    case Some{+v}:
      settle_inv(Cli.scan_error(state, Cli.E05{Cli.arg_display(x), v}),
        items0, id, err_inv(state, Cli.E05{Cli.arg_display(x), v}, items0, id,
          inv))
    case None{}:
      %eh : MInv(Cli.scan_settle(_), items0, id)
      settle_inv(Cli.scan_event(state, e), items0, id,
        push_hit(state, q, x, pol, e, items0, id, ef, ok, eo, inv))

def opt_inv(attached: Maybe<&2, String>, +state: Cli.ScanState,
    +x: Cli.ArgInfo, +q: String, +pol: Bool, -items0: List<&2, Cli.Item>,
    +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    kv: {Cli.kind_valued(Cli.info_kind(x)) == True{} : Bool},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_option(attached, state, x), items0, id):
  match attached:
    case Some{+v}:
      settle_inv(Cli.scan_value(state, x, v), items0, id,
        value_inv(state, q, x, pol, v, items0, id, ef, kv, inv))
    case None{}: (inv, (q, (pol, (ef, kv))))

def bare_inv(attached: Maybe<&2, String>, +state: Cli.ScanState,
    +x: Cli.ArgInfo, +q: String, -pol: Bool, -items0: List<&2, Cli.Item>,
    +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    kv: {Cli.kind_valued(Cli.info_kind(x)) == True{} : Bool},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_bare_option(attached, state, x), items0, id):
  match attached:
    case Some{+v}:
      settle_inv(Cli.scan_value(state, x, v), items0, id,
        value_inv(state, q, x, pol, v, items0, id, ef, kv, inv))
    case None{}:
      settle_inv(Cli.scan_value(state, x, Cli.info_bare_value(x)), items0, id,
        value_inv(state, q, x, pol, Cli.info_bare_value(x), items0, id, ef,
          kv, inv))

def kind_inv(kind: Cli.UsageKind, +k: String, +u: String, +s: String,
    +l: String, +a: List<&2, Cli.Item>, +pol: Bool,
    attached: Maybe<&2, String>, +state: Cli.ScanState, +q: String,
    -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{Cli.ArgInfo{k, u, s, l, kind, a}, pol}}
      : Maybe<&2, Cli.OptFound>},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_found_kind(kind, attached, state,
      Cli.ArgInfo{k, u, s, l, kind, a}, pol), items0, id):
  match kind:
    case Cli.FlagKind{}:
      so_inv(attached, state, Cli.ArgInfo{k, u, s, l, Cli.FlagKind{}, a}, pol,
        Cli.FlagHit{k, pol}, q, items0, id, ef,
        or_true_right(Bool.not(String.eq(k, id))), {==}, {==}, inv)
    case Cli.CountKind{}:
      so_inv(attached, state, Cli.ArgInfo{k, u, s, l, Cli.CountKind{}, a},
        pol, Cli.CountHit{k}, q, items0, id, ef,
        or_true_right(Bool.not(String.eq(k, id))), {==}, {==}, inv)
    case Cli.NegatableKind{}:
      so_inv(attached, state,
        Cli.ArgInfo{k, u, s, l, Cli.NegatableKind{}, a}, pol,
        Cli.FlagHit{k, pol}, q, items0, id, ef,
        or_true_right(Bool.not(String.eq(k, id))), {==}, {==}, inv)
    case Cli.OptionKind{+many}:
      opt_inv(attached, state, Cli.ArgInfo{k, u, s, l, Cli.OptionKind{many},
        a}, q, pol, items0, id, ef, {==}, inv)
    case Cli.BareOptionKind{}:
      bare_inv(attached, state, Cli.ArgInfo{k, u, s, l,
        Cli.BareOptionKind{}, a}, q, pol, items0, id, ef, {==}, inv)
    case Cli.PosKind{required, many}: settle_inv(state, items0, id, inv)

def found_inv(f: Cli.OptFound, attached: Maybe<&2, String>,
    +state: Cli.ScanState, +q: String, -items0: List<&2, Cli.Item>,
    +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q) == Some{f}
      : Maybe<&2, Cli.OptFound>},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_found(f, attached, state), items0, id):
  match f:
    case Cli.OptFound{x, pol}:
      match x:
        case Cli.ArgInfo{k, u, s, l, kind, a}:
          kind_inv(kind, k, u, s, l, a, pol, attached, state, q, items0, id,
            ef, inv)

def bh_inv(attached: Maybe<&2, String>, +state: Cli.ScanState,
    +event: Cli.ScanEvent, +name: String, -items0: List<&2, Cli.Item>,
    +id: String, eo: {off(event, id) == True{} : Bool},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_builtin_hit(attached, state, event, name), items0, id):
  match attached:
    case Some{+v}:
      settle_inv(Cli.scan_error(state, Cli.E05{name, v}), items0, id,
        err_inv(state, Cli.E05{name, v}, items0, id, inv))
    case None{}: push_off(state, event, items0, id, eo, inv)

def bv_inv(enabled: Bool, attached: Maybe<&2, String>, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_builtin_version(enabled, attached, state), items0, id):
  match enabled:
    case True{}:
      bh_inv(attached, state, Cli.VersionHit{}, "--version", items0, id, {==},
        inv)
    case False{}:
      settle_inv(Cli.scan_error(state, Cli.E01{"--version"}), items0, id,
        err_inv(state, Cli.E01{"--version"}, items0, id, inv))

def bo_inv(version: Bool, +name: String, attached: Maybe<&2, String>,
    +state: Cli.ScanState, -items0: List<&2, Cli.Item>, +id: String,
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_builtin_other(version, name, attached, state), items0, id):
  match version:
    case True{}:
      bv_inv(Cli.scope_version(Cli.scan_state_scope(state)), attached, state,
        items0, id, inv)
    case False{}:
      settle_inv(Cli.scan_error(state, Cli.E01{name}), items0, id,
        err_inv(state, Cli.E01{name}, items0, id, inv))

def blc_inv(help: Bool, +name: String, attached: Maybe<&2, String>,
    state: Cli.ScanState, -items0: List<&2, Cli.Item>, +id: String,
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_builtin_long_case(help, name, attached, state), items0, id):
  match help:
    case True{}:
      bh_inv(attached, state, Cli.HelpHit{True{}}, "--help", items0, id, {==},
        inv)
    case False{}:
      bo_inv(String.eq(name, "--version"), name, attached, state, items0, id,
        inv)

def lf_inv(found: Maybe<&2, Cli.OptFound>, +name: String,
    attached: Maybe<&2, String>, +state: Cli.ScanState, +q: String,
    -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q) == found
      : Maybe<&2, Cli.OptFound>},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_long_found(found, name, attached, state), items0, id):
  match found:
    case Some{f}: found_inv(f, attached, state, q, items0, id, ef, inv)
    case None{}:
      blc_inv(String.eq(name, "--help"), name, attached, state, items0, id,
        inv)

def long_inv(+token: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_long(token, state), items0, id):
  lf_inv(Cli.find_option_scope(Cli.scan_state_scope(state),
    Cli.before_equal(token)), Cli.before_equal(token),
    Cli.after_equal(token), state, Cli.before_equal(token), items0, id, {==},
    inv)

def ok_inv(state: Cli.ScanState, token: String, -items0: List<&2, Cli.Item>,
    +id: String, inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_operand_ok(state, token), items0, id):
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}:
      push_off(Cli.ScanState{scope, events, resting, count, external, issue},
        Cli.Operand{token}, items0, id, {==}, inv)

def opc_inv(allowed: Bool, state: Cli.ScanState, token: String,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_operand_case(allowed, state, token), items0, id):
  match allowed:
    case True{}: ok_inv(state, token, items0, id, inv)
    case False{}: err_inv(state, Cli.E09{token}, items0, id, inv)

def operand_inv(state: Cli.ScanState, token: String,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_operand(state, token), items0, id):
  match state:
    case Cli.ScanState{+scope, events, resting, +count, external, issue}:
      opc_inv(Cli.scope_can_take(scope, count),
        Cli.ScanState{scope, events, resting, count, external, issue}, token,
        items0, id, inv)

# What scan_short_go does with a found arg of each kind, for a head h.
def SomeEqs(h: Char) -> Type:
  (@t: String -> @st: Cli.ScanState -> @k: String -> @u: String ->
    @s: String -> @l: String -> @a: List<&2, Cli.Item> -> @p: Bool ->
    {Cli.scan_short_go(t, Cli.scan_event(st, Cli.FlagHit{k, p}),
      Cli.find_short_for_head(t, Cli.scan_event(st, Cli.FlagHit{k, p})))
      == Cli.scan_short_go(SCon{h, t}, st, Some{Cli.OptFound{
        Cli.ArgInfo{k, u, s, l, Cli.FlagKind{}, a}, p}}) : Cli.Mode}) &
  ((@t: String -> @st: Cli.ScanState -> @k: String -> @u: String ->
    @s: String -> @l: String -> @a: List<&2, Cli.Item> -> @p: Bool ->
    {Cli.scan_short_go(t, Cli.scan_event(st, Cli.CountHit{k}),
      Cli.find_short_for_head(t, Cli.scan_event(st, Cli.CountHit{k})))
      == Cli.scan_short_go(SCon{h, t}, st, Some{Cli.OptFound{
        Cli.ArgInfo{k, u, s, l, Cli.CountKind{}, a}, p}}) : Cli.Mode}) &
  ((@t: String -> @st: Cli.ScanState -> @k: String -> @u: String ->
    @s: String -> @l: String -> @a: List<&2, Cli.Item> -> @p: Bool ->
    {Cli.scan_short_go(t, Cli.scan_event(st, Cli.FlagHit{k, p}),
      Cli.find_short_for_head(t, Cli.scan_event(st, Cli.FlagHit{k, p})))
      == Cli.scan_short_go(SCon{h, t}, st, Some{Cli.OptFound{
        Cli.ArgInfo{k, u, s, l, Cli.NegatableKind{}, a}, p}}) : Cli.Mode}) &
  ((@t: String -> @st: Cli.ScanState -> @k: String -> @u: String ->
    @s: String -> @l: String -> @a: List<&2, Cli.Item> -> @p: Bool ->
    @m: Bool ->
    {Cli.scan_short_value(t, st, Cli.ArgInfo{k, u, s, l, Cli.OptionKind{m},
      a}) == Cli.scan_short_go(SCon{h, t}, st, Some{Cli.OptFound{
        Cli.ArgInfo{k, u, s, l, Cli.OptionKind{m}, a}, p}}) : Cli.Mode}) &
  ((@t: String -> @st: Cli.ScanState -> @k: String -> @u: String ->
    @s: String -> @l: String -> @a: List<&2, Cli.Item> -> @p: Bool ->
    {Cli.scan_short_bare_value(t, st, Cli.ArgInfo{k, u, s, l,
      Cli.BareOptionKind{}, a}) == Cli.scan_short_go(SCon{h, t}, st,
      Some{Cli.OptFound{Cli.ArgInfo{k, u, s, l, Cli.BareOptionKind{}, a}, p}})
      : Cli.Mode}) &
   (@t: String -> @st: Cli.ScanState -> @k: String -> @u: String ->
    @s: String -> @l: String -> @a: List<&2, Cli.Item> -> @p: Bool ->
    @r: Bool -> @m: Bool ->
    {Cli.scan_settle(st) == Cli.scan_short_go(SCon{h, t}, st,
      Some{Cli.OptFound{Cli.ArgInfo{k, u, s, l, Cli.PosKind{r, m}, a}, p}})
      : Cli.Mode})))))

# A head that is neither h nor V: an unknown one is E01.
def ShortOther(h: Char) -> Type:
  (@t: String -> @st: Cli.ScanState ->
    {Cli.scan_settle(Cli.scan_error(st, Cli.E01{String.append("-",
      Char.show(h))})) == Cli.scan_short_go(SCon{h, t}, st, None{})
      : Cli.Mode}) & SomeEqs(h)

def ShortView(h: Char) -> Type:
  {Chr{104} == h : Char} | ({Chr{86} == h : Char} | ShortOther(h))

def some_eqs_104() -> SomeEqs(Chr{104}):
  (t => st => k => u => s => l => a => p => {==},
   (t => st => k => u => s => l => a => p => {==},
    (t => st => k => u => s => l => a => p => {==},
     (t => st => k => u => s => l => a => p => m => {==},
      (t => st => k => u => s => l => a => p => {==},
       t => st => k => u => s => l => a => p => r => m => {==})))))

def some_eqs_86() -> SomeEqs(Chr{86}):
  (t => st => k => u => s => l => a => p => {==},
   (t => st => k => u => s => l => a => p => {==},
    (t => st => k => u => s => l => a => p => {==},
     (t => st => k => u => s => l => a => p => m => {==},
      (t => st => k => u => s => l => a => p => {==},
       t => st => k => u => s => l => a => p => r => m => {==})))))

# Arms: python3 tools/charsplit.py '(t => st => {==}, (F, (F, (F, (O, (F, P))))))' 104 86
# where F, O and P are SomeEqs' closures proved by {==}.
def short_view(h: Char) -> ShortView(h):
  match h:
    case Chr{U32{WCon{True{}, _}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inl{{==}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inl{{==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}}:
      Inr{Inr{(t => st => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => {==}, (t => st => k => u => s => l => a => p => m => {==}, (t => st => k => u => s => l => a => p => {==}, t => st => k => u => s => l => a => p => r => m => {==}))))))}}

def ShortIH(t: String, items0: List<&2, Cli.Item>, id: String) -> Type:
  @st: Cli.ScanState -> SInv(st, items0, id) ->
    MInv(Cli.scan_short_go(t, st, Cli.find_short_for_head(t, st)), items0, id)

def ssv_inv(value: String, +state: Cli.ScanState, +x: Cli.ArgInfo,
    +q: String, +pol: Bool, -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    kv: {Cli.kind_valued(Cli.info_kind(x)) == True{} : Bool},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_short_value_attached(value, state, x), items0, id):
  match value:
    case SNil{}: (inv, (q, (pol, (ef, kv))))
    case SCon{+c, +r}:
      settle_inv(Cli.scan_value(state, x, SCon{c, r}), items0, id,
        value_inv(state, q, x, pol, SCon{c, r}, items0, id, ef, kv, inv))

def sbv_inv(chars: String, +state: Cli.ScanState, +x: Cli.ArgInfo,
    +q: String, -pol: Bool, -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{x, pol}} : Maybe<&2, Cli.OptFound>},
    kv: {Cli.kind_valued(Cli.info_kind(x)) == True{} : Bool},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_short_bare_value(chars, state, x), items0, id):
  match chars:
    case SNil{}:
      settle_inv(Cli.scan_value(state, x, Cli.info_bare_value(x)), items0, id,
        value_inv(state, q, x, pol, Cli.info_bare_value(x), items0, id, ef,
          kv, inv))
    case SCon{+c, +r}:
      settle_inv(Cli.scan_value(state, x, Cli.short_attached(SCon{c, r})),
        items0, id, value_inv(state, q, x, pol,
          Cli.short_attached(SCon{c, r}), items0, id, ef, kv, inv))

def sg_kind(kind: Cli.UsageKind, +k: String, +u: String, +s: String,
    +l: String, +a: List<&2, Cli.Item>, +pol: Bool, -h: Char, +t: String,
    +state: Cli.ScanState, +q: String, -items0: List<&2, Cli.Item>,
    +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q)
      == Some{Cli.OptFound{Cli.ArgInfo{k, u, s, l, kind, a}, pol}}
      : Maybe<&2, Cli.OptFound>},
    inv: SInv(state, items0, id), eqs: SomeEqs(h),
    ih: ShortIH(t, items0, id)) ->
    MInv(Cli.scan_short_go(SCon{h, t}, state,
      Some{Cli.OptFound{Cli.ArgInfo{k, u, s, l, kind, a}, pol}}), items0, id):
  match kind:
    case Cli.FlagKind{}:
      match eqs:
        case (fl, rest):
          %fl(t, state, k, u, s, l, a, pol) : MInv(_, items0, id)
          ih(Cli.scan_event(state, Cli.FlagHit{k, pol}),
            push_hit(state, q, Cli.ArgInfo{k, u, s, l, Cli.FlagKind{}, a}, pol,
              Cli.FlagHit{k, pol}, items0, id, ef,
              or_true_right(Bool.not(String.eq(k, id))), {==}, inv))
    case Cli.CountKind{}:
      match eqs:
        case (fl, (co, rest)):
          %co(t, state, k, u, s, l, a, pol) : MInv(_, items0, id)
          ih(Cli.scan_event(state, Cli.CountHit{k}),
            push_hit(state, q, Cli.ArgInfo{k, u, s, l, Cli.CountKind{}, a},
              pol, Cli.CountHit{k}, items0, id, ef,
              or_true_right(Bool.not(String.eq(k, id))), {==}, inv))
    case Cli.NegatableKind{}:
      match eqs:
        case (fl, (co, (ng, rest))):
          %ng(t, state, k, u, s, l, a, pol) : MInv(_, items0, id)
          ih(Cli.scan_event(state, Cli.FlagHit{k, pol}),
            push_hit(state, q,
              Cli.ArgInfo{k, u, s, l, Cli.NegatableKind{}, a}, pol,
              Cli.FlagHit{k, pol}, items0, id, ef,
              or_true_right(Bool.not(String.eq(k, id))), {==}, inv))
    case Cli.OptionKind{+many}:
      match eqs:
        case (fl, (co, (ng, (op, rest)))):
          %op(t, state, k, u, s, l, a, pol, many) : MInv(_, items0, id)
          ssv_inv(Cli.short_attached(t), state,
            Cli.ArgInfo{k, u, s, l, Cli.OptionKind{many}, a}, q, pol, items0,
            id, ef, {==}, inv)
    case Cli.BareOptionKind{}:
      match eqs:
        case (fl, (co, (ng, (op, (ba, po))))):
          %ba(t, state, k, u, s, l, a, pol) : MInv(_, items0, id)
          sbv_inv(t, state, Cli.ArgInfo{k, u, s, l, Cli.BareOptionKind{}, a},
            q, pol, items0, id, ef, {==}, inv)
    case Cli.PosKind{+required, +many}:
      match eqs:
        case (fl, (co, (ng, (op, (ba, po))))):
          %po(t, state, k, u, s, l, a, pol, required, many) :
            MInv(_, items0, id)
          settle_inv(state, items0, id, inv)

def sg_found(found: Maybe<&2, Cli.OptFound>, -h: Char, +t: String,
    +state: Cli.ScanState, +q: String, -items0: List<&2, Cli.Item>,
    +id: String,
    ef: {Cli.find_option_scope(Cli.scan_state_scope(state), q) == found
      : Maybe<&2, Cli.OptFound>},
    inv: SInv(state, items0, id),
    nc: SInv(state, items0, id) ->
      MInv(Cli.scan_short_go(SCon{h, t}, state, None{}), items0, id),
    eqs: SomeEqs(h), ih: ShortIH(t, items0, id)) ->
    MInv(Cli.scan_short_go(SCon{h, t}, state, found), items0, id):
  match found:
    case None{}: nc(inv)
    case Some{f}:
      match f:
        case Cli.OptFound{x, pol}:
          match x:
            case Cli.ArgInfo{k, u, s, l, kind, a}:
              sg_kind(kind, k, u, s, l, a, pol, h, t, state, q, items0, id, ef,
                inv, eqs, ih)

def eqs_at(-c: Char, -h: Char, e: {c == h : Char}, x: SomeEqs(c)) ->
    SomeEqs(h):
  %e : SomeEqs(_)
  x

def help_none(-h: Char, t: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, e: {Chr{104} == h : Char},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_short_go(SCon{h, t}, state, None{}), items0, id):
  %e : MInv(Cli.scan_short_go(SCon{_, t}, state, None{}), items0, id)
  push_off(state, Cli.HelpHit{False{}}, items0, id, {==}, inv)

def sv_inv(enabled: Bool, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_short_version(enabled, state), items0, id):
  match enabled:
    case True{}: push_off(state, Cli.VersionHit{}, items0, id, {==}, inv)
    case False{}:
      settle_inv(Cli.scan_error(state, Cli.E01{"-V"}), items0, id,
        err_inv(state, Cli.E01{"-V"}, items0, id, inv))

def version_none(-h: Char, t: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, e: {Chr{86} == h : Char},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_short_go(SCon{h, t}, state, None{}), items0, id):
  %e : MInv(Cli.scan_short_go(SCon{_, t}, state, None{}), items0, id)
  sv_inv(Cli.scope_version(Cli.scan_state_scope(state)), state, items0, id,
    inv)

def other_none(+h: Char, +t: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String,
    ne: @t: String -> @st: Cli.ScanState ->
      {Cli.scan_settle(Cli.scan_error(st, Cli.E01{String.append("-",
        Char.show(h))})) == Cli.scan_short_go(SCon{h, t}, st, None{})
        : Cli.Mode},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_short_go(SCon{h, t}, state, None{}), items0, id):
  %ne(t, state) : MInv(_, items0, id)
  settle_inv(Cli.scan_error(state, Cli.E01{String.append("-",
    Char.show(h))}), items0, id, err_inv(state, Cli.E01{String.append("-",
    Char.show(h))}, items0, id, inv))

def sg_cons(+h: Char, +t: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, v: ShortView(h),
    inv: SInv(state, items0, id), ih: ShortIH(t, items0, id)) ->
    MInv(Cli.scan_short_go(SCon{h, t}, state,
      Cli.find_short_for_head(SCon{h, t}, state)), items0, id):
  match v:
    case Inl{+e}:
      sg_found(Cli.find_short_for_head(SCon{h, t}, state), h, t, state,
        String.append("-", Char.show(h)), items0, id, {==}, inv,
        iv => help_none(h, t, state, items0, id, e, iv),
        eqs_at(Chr{104}, h, e, some_eqs_104()), ih)
    case Inr{Inl{+e}}:
      sg_found(Cli.find_short_for_head(SCon{h, t}, state), h, t, state,
        String.append("-", Char.show(h)), items0, id, {==}, inv,
        iv => version_none(h, t, state, items0, id, e, iv),
        eqs_at(Chr{86}, h, e, some_eqs_86()), ih)
    case Inr{Inr{(ne, eqs)}}:
      sg_found(Cli.find_short_for_head(SCon{h, t}, state), h, t, state,
        String.append("-", Char.show(h)), items0, id, {==}, inv,
        iv => other_none(h, t, state, items0, id, ne, iv), eqs, ih)

def sg_inv(chars: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_short_go(chars, state,
      Cli.find_short_for_head(chars, state)), items0, id):
  match chars:
    case SNil{}: settle_inv(state, items0, id, inv)
    case SCon{+h, +t}:
      sg_cons(h, t, state, items0, id, short_view(h), inv,
        st => iv => sg_inv(t, st, items0, id, iv))

def dc_inv(operand: Bool, +token: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_dash_case(operand, token, state), items0, id):
  match operand:
    case True{}:
      settle_inv(Cli.scan_operand(state, token), items0, id,
        operand_inv(state, token, items0, id, inv))
    case False{}: sg_inv(String.drop(token, 1n), state, items0, id, inv)

def dash_inv(+token: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_dash_token(token, state), items0, id):
  dc_inv(Cli.scan_hyphen_candidate(state, token), token, state, items0, id,
    inv)

# ---- Descending into a subcommand ----

def b_trans_imp(a: Bool, b: Bool, c: Bool,
    e1: {Bool.or(Bool.not(a), b) == True{} : Bool},
    e2: {Bool.or(Bool.not(b), c) == True{} : Bool}) ->
    {Bool.or(Bool.not(a), c) == True{} : Bool}:
  match a:
    case True{}: b_imp(b, c, e2, e1)
    case False{}: {==}

def b_or_mono(c: Bool, a: Bool, -b: Bool,
    e: {Bool.or(Bool.not(a), b) == True{} : Bool}) ->
    {Bool.or(Bool.not(Bool.or(c, a)), Bool.or(c, b)) == True{} : Bool}:
  match c:
    case True{}: {==}
    case False{}: e

def sh_l(xs: List<&2, Cli.Seen>, +ys: List<&2, Cli.Seen>, +x: String) ->
    {Bool.or(Bool.not(sh(xs, x)), sh(List.append(&2, Cli.Seen, xs, ys), x))
      == True{} : Bool}:
  match xs:
    case Nil{}: {==}
    case Cli.SeenArg{+old, s, l} <> +tail:
      b_or_mono(String.eq(x, old), sh(tail, x),
        sh(List.append(&2, Cli.Seen, tail, ys), x), sh_l(tail, ys, x))
    case Cli.SeenSub{n} <> tail: sh_l(tail, ys, x)
    case Cli.SeenArgAlias{n} <> tail: sh_l(tail, ys, x)
    case Cli.SeenSubAlias{n} <> tail: sh_l(tail, ys, x)

# A global of I and an inherited global of id are never both there.
def gdis_c(+hgI: Bool, hI: Bool, hG: Bool, sS: Bool,
    m: {hI == False{} : Bool} -> {hgI == False{} : Bool},
    dis: {Bool.or(Bool.not(hI), Bool.not(sS)) == True{} : Bool},
    cov: {Bool.or(Bool.not(hG), sS) == True{} : Bool}) ->
    {Bool.or(Bool.not(hgI), Bool.not(hG)) == True{} : Bool}:
  match hG:
    case True{}:
      b_or_l(Bool.not(hgI), Bool.not(True{}),
        b_not_f(hgI, m(b_nand2(hI, sS, dis, cov))))
    case False{}: or_true_right(Bool.not(hgI))

# B0 at a subcommand ch of I, which lint checked against what it saw.
def desc_b(+I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>,
    +S: List<&2, Cli.Seen>, +id: String, +ch: List<&2, Cli.Item>,
    +b: {B0(I, G, S, id) == True{} : Bool},
    q3: {qt(ch, List.append(&2, Cli.Seen,
      Cli.global_entries(Cli.lint_items(I)), S), List.append(&2, Cli.Seen,
      Cli.global_entries(Cli.lint_items(ch)), List.append(&2, Cli.Seen,
      Cli.global_entries(Cli.lint_items(I)), S))) == True{} : Bool}) ->
    {B0(ch, List.append(&2, Cli.Item, Cli.global_items(I), G),
      List.append(&2, Cli.Seen, Cli.global_entries(Cli.lint_items(I)), S), id)
      == True{} : Bool}:
  +H = List.append(&2, Cli.Seen, Cli.global_entries(Cli.lint_items(I)), S)
  +gI = Cli.global_items(I)
  +qI = b0_qt(I, G, S, id, b)
  +qa = b0_qam(I, G, S, id, b)
  +cov = b0_cov(I, G, S, id, b)
  and_true(qt(ch, H, List.append(&2, Cli.Seen,
    Cli.global_entries(Cli.lint_items(ch)), H)),
    Bool.and(Bool.or(Bool.not(has(List.append(&2, Cli.Item, gI, G), id)),
      sh(H, id)), Bool.and(am1(List.append(&2, Cli.Item, gI, G), id),
      nonpos(List.append(&2, Cli.Item, gI, G)))), q3,
    and_true(Bool.or(Bool.not(has(List.append(&2, Cli.Item, gI, G), id)),
      sh(H, id)), Bool.and(am1(List.append(&2, Cli.Item, gI, G), id),
      nonpos(List.append(&2, Cli.Item, gI, G))),
      (%Equal.sym(Bool, has(List.append(&2, Cli.Item, gI, G), id),
        Bool.or(has(gI, id), has(G, id)), has_app(gI, G, id)) :
        {Bool.or(Bool.not(_), sh(H, id)) == True{} : Bool}
      b3(has(gI, id), has(G, id), sh(H, id), sh(S, id),
        b_trans_imp(has(gI, id),
          sh(Cli.global_entries(Cli.lint_items(I)), id), sh(H, id),
          gcov(I, S, H, id, qI),
          sh_l(Cli.global_entries(Cli.lint_items(I)), S, id)),
        cov, sh_up(Cli.global_entries(Cli.lint_items(I)), S, id))),
      and_true(am1(List.append(&2, Cli.Item, gI, G), id),
        nonpos(List.append(&2, Cli.Item, gI, G)),
        am1_app(gI, G, id, am1_glob(I, id, and_left(am1(I, id),
          Bool.or(Bool.not(has(I, id)), Bool.not(sh(S, id))), qa)),
          b0_am(I, G, S, id, b),
          gdis_c(has(gI, id), has(I, id), has(G, id), sh(S, id),
            e => has_glob(I, id, e), and_right(am1(I, id),
              Bool.or(Bool.not(has(I, id)), Bool.not(sh(S, id))), qa), cov)),
        nonpos_app(gI, G, gnonpos(I, S, H, qI), b0_np(I, G, S, id, b)))))

def ev_none(events: List<&2, Cli.ScanEvent>, +L: List<&2, Cli.Item>,
    +id: String, +en: {has(L, id) == False{} : Bool}) ->
    {ev_all(events, L, id) == True{} : Bool}:
  match events:
    case Nil{}: {==}
    case +e <> +t:
      and_true(acc(L, e, id), ev_all(t, L, id), acc_none(L, e, id, en),
        ev_none(t, L, id, en))

# An event an arg of the scope's globals G hits is kept; G has no arg of id,
# so an event that names id is dropped.
def ko_id(c: Bool, +k: String, +G: List<&2, Cli.Item>,
    +ch: List<&2, Cli.Item>, +e: Cli.ScanEvent, +id: String,
    ec: {String.eq(k, id) == c : Bool},
    eo: {off(e, id) == Bool.not(c) : Bool},
    hn: {has(G, id) == False{} : Bool}) ->
    {Bool.or(Bool.not(Cli.event_inherited(Some{k}, Cli.spec_items(G))),
      acc(ch, e, id)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(String, k, id, eq_reflect(k, id, ec)) :
        {Bool.or(Bool.not(Cli.event_inherited(Some{_}, Cli.spec_items(G))),
          acc(ch, e, id)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Cli.ArgInfo>,
        Cli.find_spec_info(Cli.spec_items(G), id, None{}), None{},
        Equal.trans(Maybe<&2, Cli.ArgInfo>,
          Cli.find_spec_info(Cli.spec_items(G), id, None{}),
          Cli.find_arg_info(G, id), None{}, Laws.p19_arg(G, id),
          Equal.trans(Maybe<&2, Cli.ArgInfo>, Cli.find_arg_info(G, id),
            Laws.arg_ref(G, id), None{}, Laws.p18_arg(G, id),
            ref_none(G, id, hn)))) :
        {Bool.or(Bool.not(Maybe.is_some(&2, Cli.ArgInfo, _)),
          acc(ch, e, id)) == True{} : Bool}
      {==}
    case False{}:
      b_or_r(Bool.not(Cli.event_inherited(Some{k}, Cli.spec_items(G))),
        acc(ch, e, id), acc_off(ch, e, id, eo))

def ko_hit(e: Cli.ScanEvent, +G: List<&2, Cli.Item>, +ch: List<&2, Cli.Item>,
    +id: String, hn: {has(G, id) == False{} : Bool}) ->
    {Bool.or(Bool.not(Cli.event_inherited(Cli.event_id(e), Cli.spec_items(G))),
      acc(ch, e, id)) == True{} : Bool}:
  match e:
    case Cli.FlagHit{+k, +b}:
      ko_id(String.eq(k, id), k, G, ch, Cli.FlagHit{k, b}, id, {==}, {==}, hn)
    case Cli.CountHit{+k}:
      ko_id(String.eq(k, id), k, G, ch, Cli.CountHit{k}, id, {==}, {==}, hn)
    case Cli.ValueHit{+k, +v}:
      ko_id(String.eq(k, id), k, G, ch, Cli.ValueHit{k, v}, id, {==}, {==},
        hn)
    case Cli.Operand{t}: acc_off(ch, Cli.Operand{t}, id, {==})
    case Cli.Enter{n}: acc_off(ch, Cli.Enter{n}, id, {==})
    case Cli.HelpHit{l}: acc_off(ch, Cli.HelpHit{l}, id, {==})
    case Cli.VersionHit{}: acc_off(ch, Cli.VersionHit{}, id, {==})

def kacc_off(events: List<&2, Cli.ScanEvent>, +G: List<&2, Cli.Item>,
    +ch: List<&2, Cli.Item>, +id: String,
    +hn: {has(G, id) == False{} : Bool}) ->
    {kacc(events, Cli.spec_items(G), ch, id) == True{} : Bool}:
  match events:
    case Nil{}: {==}
    case +e <> +t:
      and_true(Bool.or(Bool.not(Cli.event_inherited(Cli.event_id(e),
        Cli.spec_items(G))), acc(ch, e, id)),
        kacc(t, Cli.spec_items(G), ch, id), ko_hit(e, G, ch, id, hn),
        kacc_off(t, G, ch, id, hn))

def dI_c(c: Bool, +events: List<&2, Cli.ScanEvent>, +G2: List<&2, Cli.Item>,
    +S2: List<&2, Cli.Seen>, +ch: List<&2, Cli.Item>, +id: String,
    +name: String, ec: {has(G2, id) == c : Bool},
    cov2: {Bool.or(Bool.not(has(G2, id)), sh(S2, id)) == True{} : Bool},
    dis2: {Bool.or(Bool.not(has(ch, id)), Bool.not(sh(S2, id))) == True{}
      : Bool}) ->
    {ev_all(Cli.Enter{name} <> Cli.events_inherited(events, Cli.spec_items(G2)),
      ch, id) == True{} : Bool}:
  match c:
    case True{}:
      ev_none(Cli.Enter{name} <> Cli.events_inherited(events,
        Cli.spec_items(G2)), ch, id, b_nand2(has(ch, id), sh(S2, id), dis2,
        b_imp(has(G2, id), sh(S2, id), cov2, ec)))
    case False{}:
      and_true(acc(ch, Cli.Enter{name}, id),
        ev_all(Cli.events_inherited(events, Cli.spec_items(G2)), ch, id),
        acc_off(ch, Cli.Enter{name}, id, {==}),
        ev_kept(events, Cli.spec_items(G2), ch, id,
          kacc_off(events, G2, ch, id, ec)))

def desc_eG(+events: List<&2, Cli.ScanEvent>, +I: List<&2, Cli.Item>,
    +G: List<&2, Cli.Item>, +id: String, +name: String,
    eG: {ev_all(events, G, id) == True{} : Bool},
    eI: {ev_all(events, I, id) == True{} : Bool}) ->
    {ev_all(Cli.Enter{name} <> Cli.events_inherited(events,
      Cli.spec_items(List.append(&2, Cli.Item, Cli.global_items(I), G))),
      List.append(&2, Cli.Item, Cli.global_items(I), G), id) == True{}
      : Bool}:
  +G2 = List.append(&2, Cli.Item, Cli.global_items(I), G)
  and_true(acc(G2, Cli.Enter{name}, id),
    ev_all(Cli.events_inherited(events, Cli.spec_items(G2)), G2, id),
    acc_off(G2, Cli.Enter{name}, id, {==}),
    ev_kept(events, Cli.spec_items(G2), G2, id,
      kacc_all(events, Cli.spec_items(G2), G2, id,
        ev_app(events, Cli.global_items(I), G, id,
          ev_glob(events, I, id, eI), eG))))

def desc_ei(p: List<&2, String>, -name: String, -items0: List<&2, Cli.Item>,
    -I: List<&2, Cli.Item>, -ch: List<&2, Cli.Item>,
    ei: {hi(p, items0) == I : List<&2, Cli.Item>},
    c1: {Cli.find_sub_go(I, name, None{}) == Some{Cli.SubFound{name, ch}}
      : Maybe<&2, Cli.SubFound>}) ->
    {hi(List.append(&2, String, p, [name]), items0) == ch
      : List<&2, Cli.Item>}:
  %Equal.sym(List<&2, Cli.Item>, hi(List.append(&2, String, p, [name]),
    items0), Cli.sub_items(Cli.find_sub(hi(p, items0), name)),
    hi_snoc(p, name, items0)) : {_ == ch : List<&2, Cli.Item>}
  %Equal.sym(List<&2, Cli.Item>, hi(p, items0), I, ei) :
    {Cli.sub_items(Cli.find_sub(_, name)) == ch : List<&2, Cli.Item>}
  %Equal.sym(Maybe<&2, Cli.SubFound>, Cli.find_sub_go(I, name, None{}),
    Some{Cli.SubFound{name, ch}}, c1) :
    {Cli.sub_items(_) == ch : List<&2, Cli.Item>}
  {==}

def desc_eg(p: List<&2, String>, -name: String, -items0: List<&2, Cli.Item>,
    -I: List<&2, Cli.Item>, -G: List<&2, Cli.Item>,
    ei: {hi(p, items0) == I : List<&2, Cli.Item>},
    eg: {hg(p, items0, Nil{}) == G : List<&2, Cli.Item>}) ->
    {hg(List.append(&2, String, p, [name]), items0, Nil{})
      == List.append(&2, Cli.Item, Cli.global_items(I), G)
      : List<&2, Cli.Item>}:
  %Equal.sym(List<&2, Cli.Item>, hg(List.append(&2, String, p, [name]),
    items0, Nil{}), List.append(&2, Cli.Item, Cli.global_items(hi(p, items0)),
    hg(p, items0, Nil{})), hg_snoc(p, name, items0, Nil{})) :
    {_ == List.append(&2, Cli.Item, Cli.global_items(I), G)
      : List<&2, Cli.Item>}
  %Equal.sym(List<&2, Cli.Item>, hi(p, items0), I, ei) :
    {List.append(&2, Cli.Item, Cli.global_items(_), hg(p, items0, Nil{}))
      == List.append(&2, Cli.Item, Cli.global_items(I), G)
      : List<&2, Cli.Item>}
  %Equal.sym(List<&2, Cli.Item>, hg(p, items0, Nil{}), G, eg) :
    {List.append(&2, Cli.Item, Cli.global_items(I), _)
      == List.append(&2, Cli.Item, Cli.global_items(I), G)
      : List<&2, Cli.Item>}
  {==}

def desc_tuple(+p: List<&2, String>, +I: List<&2, Cli.Item>,
    +G: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>, +name: String,
    +ch: List<&2, Cli.Item>, +events: List<&2, Cli.ScanEvent>,
    -items0: List<&2, Cli.Item>, +id: String,
    c: Canon(I, name, ch, S, List.append(&2, Cli.Seen,
      Cli.global_entries(Cli.lint_items(I)), S)),
    +ei: {hi(p, items0) == I : List<&2, Cli.Item>},
    eg: {hg(p, items0, Nil{}) == G : List<&2, Cli.Item>},
    +b: {B0(I, G, S, id) == True{} : Bool},
    +eG: {ev_all(events, G, id) == True{} : Bool},
    +eI: {ev_all(events, I, id) == True{} : Bool}) ->
    ScInv(Cli.Scope{List.append(&2, String, p, [name]), Cli.spec_node(ch,
      Cli.spec_items(List.append(&2, Cli.Item, Cli.global_items(I), G)))},
      Cli.Enter{name} <> Cli.events_inherited(events,
        Cli.spec_items(List.append(&2, Cli.Item, Cli.global_items(I), G))),
      items0, id):
  match c:
    case (c1, (c2, c3)):
      +G2 = List.append(&2, Cli.Item, Cli.global_items(I), G)
      +H = List.append(&2, Cli.Seen, Cli.global_entries(Cli.lint_items(I)), S)
      +b2 = desc_b(I, G, S, id, ch, b, c3)
      (List.append(&2, String, p, [name]), (ch, (G2, (H, ({==},
        (desc_ei(p, name, items0, I, ch, ei, c1),
         (desc_eg(p, name, items0, I, G, ei, eg),
          (b2, (desc_eG(events, I, G, id, name, eG, eI),
           dI_c(has(G2, id), events, G2, H, ch, id, name, {==},
             b0_cov(ch, G2, H, id, b2),
             and_right(am1(ch, id), Bool.or(Bool.not(has(ch, id)),
               Bool.not(sh(H, id))), b0_qam(ch, G2, H, id, b2))))))))))))

def key_found(m: Maybe<&2, Cli.SubKey>) -> Maybe<&2, Cli.SubFound>:
  match m:
    case None{}: None{}
    case Some{k}:
      match k:
        case Cli.SubKey{n, a, c}: Some{Cli.SubFound{n, c}}

def skf(m: Maybe<&2, Cli.SubFound>, -name: String, -al: List<&2, String>,
    -ch: List<&2, Cli.Item>,
    e: {Laws.sub_key_of(m) == Some{Cli.SubKey{name, al, ch}}
      : Maybe<&2, Cli.SubKey>}) ->
    {m == Some{Cli.SubFound{name, ch}} : Maybe<&2, Cli.SubFound>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{Cli.SubFound{name, ch}}
        : Maybe<&2, Cli.SubFound>}, false_true_absurd(Equal.cong(
        Maybe<&2, Cli.SubKey>, Bool, x => Maybe.is_some(&2, Cli.SubKey, x),
        None{}, Some{Cli.SubKey{name, al, ch}}, e)))
    case Some{sf}:
      match sf:
        case Cli.SubFound{n, c}:
          Equal.cong(Maybe<&2, Cli.SubKey>, Maybe<&2, Cli.SubFound>,
            x => key_found(x), Some{Cli.SubKey{n, Cli.find_aliases(c), c}},
            Some{Cli.SubKey{name, al, ch}}, e)

# Entering a subcommand the scope finds keeps the invariant.
def descend_inv(state: Cli.ScanState, sub: Cli.SubKey, +q: String,
    -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.scope_find_sub(Cli.scan_state_scope(state), q) == Some{sub}
      : Maybe<&2, Cli.SubKey>},
    inv: SInv(state, items0, id)) ->
    SInv(Cli.scan_descend(state, sub), items0, id):
  match state:
    case Cli.ScanState{scope, events, resting, count, external, issue}:
      match sub:
        case Cli.SubKey{+name, al, +ch}:
          match inv:
            case (+p, (+I, (+G, (+S, (+es, (ei, (eg, (+b, (eG, eI))))))))):
              %Equal.sym(Cli.Scope, scope, Cli.Scope{p, Cli.spec_node(I,
                Cli.spec_items(G))}, es) :
                SInv(Cli.scan_descend(Cli.ScanState{_, events, resting,
                count, external, issue}, Cli.SubKey{name, al, ch}), items0, id)
              %Equal.sym(List<&2, Cli.SpecItem>,
                Cli.spec_inherit(Cli.spec_node(I, Cli.spec_items(G))),
                Cli.spec_items(List.append(&2, Cli.Item, Cli.global_items(I),
                  G)), Laws.p19_inherit(I, G)) :
                ScInv(Cli.Scope{List.append(&2, String, p, [name]),
                  Cli.spec_node(ch, _)}, Cli.Enter{name} <>
                  Cli.events_inherited(events, _), items0, id)
              desc_tuple(p, I, G, S, name, ch, events, items0, id,
                canon(I, q, S, List.append(&2, Cli.Seen,
                  Cli.global_entries(Cli.lint_items(I)), S), name, ch,
                  b0_qt(I, G, S, id, b),
                  skf(Cli.find_sub(I, q), name, al, ch,
                    Equal.trans(Maybe<&2, Cli.SubKey>,
                      Laws.sub_key_of(Cli.find_sub(I, q)),
                      Cli.scope_find_sub(Cli.Scope{p, Cli.spec_node(I,
                        Cli.spec_items(G))}, q),
                      Some{Cli.SubKey{name, al, ch}},
                      Equal.sym(Maybe<&2, Cli.SubKey>,
                        Cli.scope_find_sub(Cli.Scope{p, Cli.spec_node(I,
                          Cli.spec_items(G))}, q),
                        Laws.sub_key_of(Cli.find_sub(I, q)),
                        Laws.p19_sub(I, Cli.spec_items(G), p, q)),
                      (%es : {Cli.scope_find_sub(_, q)
                        == Some{Cli.SubKey{name, al, ch}}
                        : Maybe<&2, Cli.SubKey>}
                      ef)))),
                ei, eg, b, eG, eI)

# ---- Words, tails, fetches, and the whole scan ----

def su_inv(allow: Bool, +state: Cli.ScanState, +token: String,
    -items0: List<&2, Cli.Item>, -id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_sub_unknown(allow, state, token), items0, id):
  match allow:
    case True{}: inv
    case False{}: err_inv(state, Cli.E02{token}, items0, id, inv)

def sf_inv(found: Maybe<&2, Cli.SubKey>, +state: Cli.ScanState,
    +token: String, -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.scope_find_sub(Cli.scan_state_scope(state), token) == found
      : Maybe<&2, Cli.SubKey>},
    inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_sub_found(found, state, token), items0, id):
  match found:
    case Some{+sub}:
      settle_inv(Cli.scan_descend(state, sub), items0, id,
        descend_inv(state, sub, token, items0, id, ef, inv))
    case None{}:
      su_inv(Cli.scope_external(Cli.scan_state_scope(state)), state, token,
        items0, id, inv)

def nsc_inv(help: Bool, +token: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_non_option_sub_case(help, token, state), items0, id):
  match help:
    case True{}: inv
    case False{}:
      sf_inv(Cli.scope_find_sub(Cli.scan_state_scope(state), token), state,
        token, items0, id, {==}, inv)

def nc_inv(has_sub: Bool, +token: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_non_option_case(has_sub, token, state), items0, id):
  match has_sub:
    case True{}:
      nsc_inv(String.eq(token, "help"), token, state, items0, id, inv)
    case False{}:
      settle_inv(Cli.scan_operand(state, token), items0, id,
        operand_inv(state, token, items0, id, inv))

def tc_inv(kind: Cli.TokenClass, +token: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_token_case(kind, token, state), items0, id):
  match kind:
    case Cli.LongToken{}: long_inv(token, state, items0, id, inv)
    case Cli.DashToken{}: dash_inv(token, state, items0, id, inv)
    case Cli.WordToken{}:
      nc_inv(Cli.scope_has_sub(Cli.scan_state_scope(state)), token, state,
        items0, id, inv)

def open_inv(dash: Bool, +state: Cli.ScanState, +token: String,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    MInv(Cli.scan_open(dash, state, token), items0, id):
  match dash:
    case True{}: inv
    case False{}:
      tc_inv(Cli.token_class(token), token, state, items0, id, inv)

def fc_inv(help: Maybe<&2, Bool>, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    TInv(Cli.scan_faulted_case(help, state), items0, id):
  match help:
    case Some{l}: push_off(state, Cli.HelpHit{l}, items0, id, {==}, inv)
    case None{}: inv

def faulted_inv(+state: Cli.ScanState, +token: String,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    TInv(Cli.scan_faulted(state, token), items0, id):
  fc_inv(Cli.help_flag(token), state, items0, id, inv)

def hm_inv(help: Maybe<&2, Bool>, +token: String, +state: Cli.ScanState,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id)) ->
    TInv(Cli.help_missing_case(help, token, state), items0, id):
  match help:
    case Some{l}: push_off(state, Cli.HelpHit{l}, items0, id, {==}, inv)
    case None{}:
      err_inv(state, Cli.unknown_fault(String.starts_with(token, "-"), token),
        items0, id, inv)

def hw_inv(found: Maybe<&2, Cli.SubKey>, +state: Cli.ScanState,
    +token: String, -items0: List<&2, Cli.Item>, +id: String,
    ef: {Cli.scope_find_sub(Cli.scan_state_scope(state), token) == found
      : Maybe<&2, Cli.SubKey>},
    inv: SInv(state, items0, id)) ->
    TInv(Cli.help_walk(found, state, token), items0, id):
  match found:
    case Some{sub}: descend_inv(state, sub, token, items0, id, ef, inv)
    case None{}: hm_inv(Cli.help_flag(token), token, state, items0, id, inv)

def tail_inv(tail: Cli.Tail, +token: String, -items0: List<&2, Cli.Item>,
    +id: String, inv: TInv(tail, items0, id)) ->
    TInv(Cli.scan_tail(tail, token), items0, id):
  match tail:
    case Cli.Faulted{state}: faulted_inv(state, token, items0, id, inv)
    case Cli.Walk{+state}:
      hw_inv(Cli.scope_find_sub(Cli.scan_state_scope(state), token), state,
        token, items0, id, {==}, inv)
    case Cli.Stopped{state}: inv

def fr_inv(allowed: Bool, +state: Cli.ScanState, +info: Cli.ArgInfo,
    +token: String, -items0: List<&2, Cli.Item>, +id: String,
    inv: SInv(state, items0, id), fi: FInv(state, info)) ->
    MInv(Cli.scan_fetch_result(allowed, state, info, token), items0, id):
  match allowed:
    case True{}:
      match fi:
        case (+q, (pol, (ef, kv))):
          settle_inv(Cli.scan_value(state, info, token), items0, id,
            value_inv(state, q, info, pol, token, items0, id, ef, kv, inv))
    case False{}:
      faulted_inv(Cli.scan_error(state, Cli.E03{Cli.arg_display(info)}), token,
        items0, id, err_inv(state, Cli.E03{Cli.arg_display(info)}, items0, id,
          inv))

def fetch_inv(+state: Cli.ScanState, +info: Cli.ArgInfo, +token: String,
    -items0: List<&2, Cli.Item>, +id: String, inv: SInv(state, items0, id),
    fi: FInv(state, info)) ->
    MInv(Cli.scan_fetch(state, info, token), items0, id):
  fr_inv(Cli.fetch_allowed(Cli.scan_state_scope(state), info, token), state,
    info, token, items0, id, inv, fi)

# Every mode the scan reaches keeps the invariant.
def go_inv(tokens: List<&2, String>, mode: Cli.Mode,
    -items0: List<&2, Cli.Item>, +id: String, inv: MInv(mode, items0, id)) ->
    MInv(Cli.scan_go(tokens, mode), items0, id):
  match tokens:
    case Nil{}:
      match mode:
        case Cli.Capture{state, name}:
          ext_inv(state, name, Nil{}, items0, id, inv)
        case Cli.Open{state}: inv
        case Cli.Fetch{state, info}: inv
        case Cli.Operands{state, ended}: inv
        case Cli.Closed{tail}: inv
    case +token <> +rest:
      match mode:
        case Cli.Capture{state, name}:
          ext_inv(state, name, token <> rest, items0, id, inv)
        case Cli.Open{+state}:
          go_inv(rest, Cli.scan_open(String.eq(token, "--"), state, token),
            items0, id, open_inv(String.eq(token, "--"), state, token, items0,
              id, inv))
        case Cli.Fetch{+state, +info}:
          match inv:
            case (si, fi):
              go_inv(rest, Cli.scan_fetch(state, info, token), items0, id,
                fetch_inv(state, info, token, items0, id, si, fi))
        case Cli.Operands{+state, ended}:
          go_inv(rest, Cli.Operands{Cli.scan_operand(state, token), ended},
            items0, id, operand_inv(state, token, items0, id, inv))
        case Cli.Closed{+tail}:
          go_inv(rest, Cli.Closed{Cli.scan_tail(tail, token)}, items0, id,
            tail_inv(tail, token, items0, id, inv))

def tclose_inv(tail: Cli.Tail, -items0: List<&2, Cli.Item>, +id: String,
    inv: TInv(tail, items0, id)) ->
    SInv(Cli.scan_tail_close(tail), items0, id):
  match tail:
    case Cli.Faulted{state}: inv
    case Cli.Walk{state}:
      push_off(state, Cli.HelpHit{True{}}, items0, id, {==}, inv)
    case Cli.Stopped{state}: inv

def close_inv(mode: Cli.Mode, -items0: List<&2, Cli.Item>, +id: String,
    inv: MInv(mode, items0, id)) -> SInv(Cli.scan_close(mode), items0, id):
  match mode:
    case Cli.Open{state}: inv
    case Cli.Fetch{state, info}:
      match inv:
        case (si, fi):
          err_inv(state, Cli.E03{Cli.arg_display(info)}, items0, id, si)
    case Cli.Operands{state, ended}: inv
    case Cli.Capture{state, name}: ext_inv(state, name, [], items0, id, inv)
    case Cli.Closed{tail}: tclose_inv(tail, items0, id, inv)

def seen_app_nil(xs: List<&2, Cli.Seen>) ->
    {List.append(&2, Cli.Seen, xs, Nil{}) == xs : List<&2, Cli.Seen>}:
  match xs:
    case Nil{}: {==}
    case h <> t:
      %Equal.sym(List<&2, Cli.Seen>, List.append(&2, Cli.Seen, t, Nil{}), t,
        seen_app_nil(t)) : {h <> _ == h <> t : List<&2, Cli.Seen>}
      {==}

# The scan starts at the root with no events.
def start_inv(+items0: List<&2, Cli.Item>, -n: String, -a: String,
    +id: String,
    q: {qt(items0, Nil{}, Cli.global_entries(Cli.lint_items(items0)))
      == True{} : Bool}) ->
    SInv(Cli.scan_start(Cli.Cmd{n, a, items0}), items0, id):
  +H = Cli.global_entries(Cli.lint_items(items0))
  (Nil{}, (items0, (Nil{}, (Nil{}, ({==}, ({==}, ({==},
    (and_true(qt(items0, Nil{}, List.append(&2, Cli.Seen, H, Nil{})), True{},
      (%Equal.sym(List<&2, Cli.Seen>, List.append(&2, Cli.Seen, H, Nil{}), H,
        seen_app_nil(H)) : {qt(items0, Nil{}, _) == True{} : Bool}
      q), {==}),
    ({==}, {==})))))))))

# What a whole scan of argv keeps.
def scan_inv(+items0: List<&2, Cli.Item>, +n: String, +a: String,
    +argv: List<&2, String>, +id: String,
    q: {qt(items0, Nil{}, Cli.global_entries(Cli.lint_items(items0)))
      == True{} : Bool}) ->
    SInv(Cli.scan_close(Cli.scan_go(argv, Cli.Open{Cli.scan_start(
      Cli.Cmd{n, a, items0})})), items0, id):
  close_inv(Cli.scan_go(argv, Cli.Open{Cli.scan_start(Cli.Cmd{n, a, items0})}),
    items0, id, go_inv(argv, Cli.Open{Cli.scan_start(Cli.Cmd{n, a, items0})},
      items0, id, start_inv(items0, n, a, id, q)))

# P21 parse: what resolve_scope builds keeps, for the arg the verdict judges,
# a field that arg's kind and attrs accept, and an accepted parse keeps it.

# No field of fields has key id.
def nokey(fields: List<&2, Cli.Field>, +id: String) -> Bool:
  match fields:
    case Nil{}: True{}
    case Cli.Field{key, values, source} <> tail:
      Bool.and(Bool.not(String.eq(key, id)), nokey(tail, id))

def nokey_app(xs: List<&2, Cli.Field>, +ys: List<&2, Cli.Field>, +id: String,
    +nx: {nokey(xs, id) == True{} : Bool},
    ny: {nokey(ys, id) == True{} : Bool}) ->
    {nokey(List.append(&2, Cli.Field, xs, ys), id) == True{} : Bool}:
  match xs:
    case Nil{}: ny
    case Cli.Field{+key, values, source} <> +tail:
      and_true(Bool.not(String.eq(key, id)),
        nokey(List.append(&2, Cli.Field, tail, ys), id),
        and_left(Bool.not(String.eq(key, id)), nokey(tail, id), nx),
        nokey_app(tail, ys, id, and_right(Bool.not(String.eq(key, id)),
          nokey(tail, id), nx), ny))

def key_off(+key: String, +tail: List<&2, Cli.Field>, +id: String,
    e: {Bool.and(Bool.not(String.eq(key, id)), nokey(tail, id)) == True{}
      : Bool}) -> {String.eq(key, id) == False{} : Bool}:
  nt_f(String.eq(key, id), and_left(Bool.not(String.eq(key, id)),
    nokey(tail, id), e))

def fr_none(ys: List<&2, Cli.Field>, +id: String,
    +e: {nokey(ys, id) == True{} : Bool}) ->
    {Laws.field_ref(ys, id) == Cli.Field{id, [], Cli.Absent{}} : Cli.Field}:
  match ys:
    case Nil{}: {==}
    case Cli.Field{+key, values, source} <> +tail:
      %Equal.sym(Bool, String.eq(key, id), False{},
        key_off(key, tail, id, e)) :
        {Bool.pick(Cli.Field, _, Cli.Field{key, values, source},
          Laws.field_ref(tail, id)) == Cli.Field{id, [], Cli.Absent{}}
          : Cli.Field}
      fr_none(tail, id, and_right(Bool.not(String.eq(key, id)),
        nokey(tail, id), e))

# field_ref skips a prefix with no field of id.
def fr_skip(xs: List<&2, Cli.Field>, +ys: List<&2, Cli.Field>, +id: String,
    +e: {nokey(xs, id) == True{} : Bool}) ->
    {Laws.field_ref(List.append(&2, Cli.Field, xs, ys), id)
      == Laws.field_ref(ys, id) : Cli.Field}:
  match xs:
    case Nil{}: {==}
    case Cli.Field{+key, values, source} <> +tail:
      %Equal.sym(Bool, String.eq(key, id), False{},
        key_off(key, tail, id, e)) :
        {Bool.pick(Cli.Field, _, Cli.Field{key, values, source},
          Laws.field_ref(List.append(&2, Cli.Field, tail, ys), id))
          == Laws.field_ref(ys, id) : Cli.Field}
      fr_skip(tail, ys, id, and_right(Bool.not(String.eq(key, id)),
        nokey(tail, id), e))

# field_ref ignores a suffix with no field of id.
def fr_skip2(xs: List<&2, Cli.Field>, +ys: List<&2, Cli.Field>, +id: String,
    e: {nokey(ys, id) == True{} : Bool}) ->
    {Laws.field_ref(List.append(&2, Cli.Field, xs, ys), id)
      == Laws.field_ref(xs, id) : Cli.Field}:
  match xs:
    case Nil{}: fr_none(ys, id, e)
    case Cli.Field{+key, +values, +source} <> +tail:
      Equal.cong(Cli.Field, Cli.Field,
        x => Bool.pick(Cli.Field, String.eq(key, id),
          Cli.Field{key, values, source}, x),
        Laws.field_ref(List.append(&2, Cli.Field, tail, ys), id),
        Laws.field_ref(tail, id), fr_skip2(tail, ys, id, e))

def fsrc(f: Cli.Field) -> Cli.Src:
  match f:
    case Cli.Field{key, values, source}: source

def fs_pick(c: Bool, -s: Cli.Src, -key: String, -values: List<&2, String>,
    -rs: Cli.Src, -rf: Cli.Field, e: {rs == fsrc(rf) : Cli.Src}) ->
    {Bool.pick(Cli.Src, c, s, rs) == fsrc(Bool.pick(Cli.Field, c,
      Cli.Field{key, values, s}, rf)) : Cli.Src}:
  match c:
    case True{}: {==}
    case False{}: e

# field_source reads the source of the field field_ref finds.
def fs_ref(fields: List<&2, Cli.Field>, +id: String) ->
    {Cli.field_source(fields, id) == fsrc(Laws.field_ref(fields, id))
      : Cli.Src}:
  match fields:
    case Nil{}: {==}
    case Cli.Field{+key, values, source} <> +tail:
      fs_pick(String.eq(key, id), source, key, values,
        Cli.field_source(tail, id), Laws.field_ref(tail, id),
        fs_ref(tail, id))

# A field for the judged arg: values fgood accepts when resolution gave
# them, and none, with no default, when it gave nothing.
def AbsentOk(vs: List<&2, String>, attrs: List<&2, Cli.Item>) -> Type:
  match vs:
    case Nil{}:
      {Maybe.is_some(&2, String, Cli.find_default(attrs)) == False{} : Bool}
    case v <> t: Empty

def FRs(src: Cli.Src, kind: Cli.UsageKind, attrs: List<&2, Cli.Item>,
    vs: List<&2, String>) -> Type:
  match src:
    case Cli.Argv{}: {fgood(kind, attrs, vs) == True{} : Bool}
    case Cli.Env{}: {fgood(kind, attrs, vs) == True{} : Bool}
    case Cli.Default{}: {fgood(kind, attrs, vs) == True{} : Bool}
    case Cli.Absent{}: AbsentOk(vs, attrs)

def FR(f: Cli.Field, kind: Cli.UsageKind, attrs: List<&2, Cli.Item>) ->
    Type:
  match f:
    case Cli.Field{key, values, source}: FRs(source, kind, attrs, values)

# A build with no field of id.
def NK(b: Cli.FieldBuild, id: String) -> Type:
  match b:
    case Cli.Built{fields}: {nokey(fields, id) == True{} : Bool}
    case Cli.BuildFault{fault}: Unit

# A build whose field of id the judged arg accepts.
def OW(b: Cli.FieldBuild, id: String, kind: Cli.UsageKind,
    attrs: List<&2, Cli.Item>) -> Type:
  match b:
    case Cli.Built{fields}: FR(Laws.field_ref(fields, id), kind, attrs)
    case Cli.BuildFault{fault}: Unit

def nk_built(+fields: List<&2, Cli.Field>, b2: Cli.FieldBuild, +id: String,
    n1: {nokey(fields, id) == True{} : Bool}, n2: NK(b2, id)) ->
    NK(Cli.combine_built(fields, b2), id):
  match b2:
    case Cli.Built{more}: nokey_app(fields, more, id, n1, n2)
    case Cli.BuildFault{fault}: Unit{}

def nk_comb(b1: Cli.FieldBuild, b2: Cli.FieldBuild, +id: String,
    n1: NK(b1, id), n2: NK(b2, id)) -> NK(Cli.combine_build(b1, b2), id):
  match b1:
    case Cli.Built{fields}: nk_built(fields, b2, id, n1, n2)
    case Cli.BuildFault{fault}: Unit{}

def ow_built(+fields: List<&2, Cli.Field>, b2: Cli.FieldBuild, +id: String,
    -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>,
    o1: FR(Laws.field_ref(fields, id), kind, attrs), n2: NK(b2, id)) ->
    OW(Cli.combine_built(fields, b2), id, kind, attrs):
  match b2:
    case Cli.Built{more}:
      %Equal.sym(Cli.Field,
        Laws.field_ref(List.append(&2, Cli.Field, fields, more), id),
        Laws.field_ref(fields, id), fr_skip2(fields, more, id, n2)) :
        FR(_, kind, attrs)
      o1
    case Cli.BuildFault{fault}: Unit{}

# The arg's own build, then builds with no field of id.
def ow_nk(b1: Cli.FieldBuild, b2: Cli.FieldBuild, +id: String,
    -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>,
    o1: OW(b1, id, kind, attrs), n2: NK(b2, id)) ->
    OW(Cli.combine_build(b1, b2), id, kind, attrs):
  match b1:
    case Cli.Built{fields}: ow_built(fields, b2, id, kind, attrs, o1, n2)
    case Cli.BuildFault{fault}: Unit{}

def nko_built(+fields: List<&2, Cli.Field>, b2: Cli.FieldBuild, +id: String,
    -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>,
    n1: {nokey(fields, id) == True{} : Bool}, o2: OW(b2, id, kind, attrs)) ->
    OW(Cli.combine_built(fields, b2), id, kind, attrs):
  match b2:
    case Cli.Built{more}:
      %Equal.sym(Cli.Field,
        Laws.field_ref(List.append(&2, Cli.Field, fields, more), id),
        Laws.field_ref(more, id), fr_skip(fields, more, id, n1)) :
        FR(_, kind, attrs)
      o2
    case Cli.BuildFault{fault}: Unit{}

# Builds with no field of id, then the arg's own build.
def nk_ow(b1: Cli.FieldBuild, b2: Cli.FieldBuild, +id: String,
    -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>,
    n1: NK(b1, id), o2: OW(b2, id, kind, attrs)) ->
    OW(Cli.combine_build(b1, b2), id, kind, attrs):
  match b1:
    case Cli.Built{fields}: nko_built(fields, b2, id, kind, attrs, n1, o2)
    case Cli.BuildFault{fault}: Unit{}

def one_nk(+k: String, -vs: List<&2, String>, -src: Cli.Src, +id: String,
    ec: {String.eq(k, id) == False{} : Bool}) ->
    NK(Cli.Built{[Cli.Field{k, vs, src}]}, id):
  %Equal.sym(Bool, String.eq(k, id), False{}, ec) :
    {Bool.and(Bool.not(_), True{}) == True{} : Bool}
  {==}

def one_ow(+id: String, -vs: List<&2, String>, -src: Cli.Src,
    -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>,
    fr: FRs(src, kind, attrs, vs)) ->
    OW(Cli.Built{[Cli.Field{id, vs, src}]}, id, kind, attrs):
  %Equal.sym(Bool, String.eq(id, id), True{}, string_eq_refl(id)) :
    FR(Bool.pick(Cli.Field, _, Cli.Field{id, vs, src},
      Cli.Field{id, [], Cli.Absent{}}), kind, attrs)
  fr

# An arg other than id builds no field of id.
def rev_nk(found: Maybe<&2, Cli.Bad>, info: Cli.ArgInfo, -name: String,
    -value: String, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    NK(Cli.resolve_env_valid(found, info, name, value), id):
  match found:
    case Some{Cli.Bad{bad, why}}: Unit{}
    case None{}:
      match info:
        case Cli.ArgInfo{k, u, s, l, kind, attrs}:
          one_nk(k, Cli.env_values(kind, attrs, value), Cli.Env{}, id, ec)

def rd_nk(found: Maybe<&2, String>, info: Cli.ArgInfo, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    NK(Cli.resolve_default(found, info), id):
  match found:
    case None{}: {==}
    case Some{value}:
      match info:
        case Cli.ArgInfo{k, u, s, l, kind, attrs}:
          one_nk(k, Cli.env_values(kind, attrs, value), Cli.Default{}, id,
            ec)

def red_nk(found: Maybe<&2, Cli.EnvValue>, +info: Cli.ArgInfo, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    NK(Cli.resolve_env_default(found, info), id):
  match found:
    case Some{Cli.EnvValue{name, +value}}:
      rev_nk(Cli.value_issue(Cli.info_kind(info), Cli.info_attrs(info),
        value), info, name, value, id, ec)
    case None{}: rd_nk(Cli.info_default(info), info, id, ec)

def rag_nk_seen(seen: Bool, -values: List<&2, String>, -count: Nat,
    +info: Cli.ArgInfo, h: Cli.Host, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    NK(Cli.resolve_argv_gather(Cli.Gather{seen, values, count}, info, h),
      id):
  match seen:
    case True{}:
      match info:
        case Cli.ArgInfo{k, u, s, l, kind, attrs}:
          one_nk(k, Cli.apply_delim(Cli.find_delim(attrs),
            List.reverse(&2, String, values)), Cli.Argv{}, id, ec)
    case False{}: red_nk(Cli.host_env(h, Cli.info_envs(info)), info, id, ec)

def rag_nk(g: Cli.Gather, +info: Cli.ArgInfo, h: Cli.Host, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    NK(Cli.resolve_argv_gather(g, info, h), id):
  match g:
    case Cli.Gather{seen, values, count}:
      rag_nk_seen(seen, values, count, info, h, id, ec)

def rf_nk(+info: Cli.ArgInfo, events: List<&2, Cli.ScanEvent>, h: Cli.Host,
    +id: String, ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    NK(Cli.resolve_option(info, events, h), id):
  rag_nk(Cli.gather_arg(events, info), info, h, id, ec)

def pvr_nk(found: Maybe<&2, Cli.Bad>, info: Cli.ArgInfo,
    -values: List<&2, String>, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    NK(Cli.pos_valid_result(found, info, values), id):
  match found:
    case Some{Cli.Bad{bad, why}}: Unit{}
    case None{}:
      match info:
        case Cli.ArgInfo{k, u, s, l, kind, attrs}:
          one_nk(k, values, Cli.Argv{}, id, ec)

def rp_nk(+info: Cli.ArgInfo, values: List<&2, String>, h: Cli.Host,
    +id: String, ec: {String.eq(Cli.info_id(info), id) == False{} : Bool}) ->
    NK(Cli.resolve_pos(info, values, h), id):
  match values:
    case Nil{}: red_nk(Cli.host_env(h, Cli.info_envs(info)), info, id, ec)
    case +v <> +vs:
      pvr_nk(Cli.first_bad(Cli.apply_delim(Cli.find_delim(
        Cli.info_attrs(info)), v <> vs), Cli.info_attrs(info)), info,
        Cli.apply_delim(Cli.find_delim(Cli.info_attrs(info)), v <> vs), id,
        ec)

# The judged arg's own build: a default with no field is no default, and a
# value from env, a default or the argv is one fgood accepts.
def rd_pg(found: Maybe<&2, String>, +id: String, -u: String, -s: String,
    -l: String, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    okd: DefaultOk(found, kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    e: {Cli.find_default(attrs) == found : Maybe<&2, String>}) ->
    OW(Cli.resolve_default(found, Cli.ArgInfo{id, u, s, l, kind, attrs}), id,
      kind, attrs):
  match found:
    case None{}:
      Equal.cong(Maybe<&2, String>, Bool, x => Maybe.is_some(&2, String, x),
        Cli.find_default(attrs), None{}, e)
    case Some{+value}:
      (oka, oki) = okd
      one_ow(id, Cli.env_values(kind, attrs, value), Cli.Default{}, kind,
        attrs, env_good(kind, attrs, value, oki, okl))

def rev_pg(found: Maybe<&2, Cli.Bad>, +id: String, -u: String, -s: String,
    -l: String, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    -name: String, +value: String, okl: DelimOk(Cli.find_delim(attrs), kind),
    e: {Cli.value_issue(kind, attrs, value) == found : Maybe<&2, Cli.Bad>}) ->
    OW(Cli.resolve_env_valid(found, Cli.ArgInfo{id, u, s, l, kind, attrs},
      name, value), id, kind, attrs):
  match found:
    case Some{Cli.Bad{bad, why}}: Unit{}
    case None{}:
      one_ow(id, Cli.env_values(kind, attrs, value), Cli.Env{}, kind, attrs,
        env_good(kind, attrs, value, e, okl))

def red_pg(found: Maybe<&2, Cli.EnvValue>, +id: String, -u: String,
    -s: String, -l: String, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind)) ->
    OW(Cli.resolve_env_default(found, Cli.ArgInfo{id, u, s, l, kind, attrs}),
      id, kind, attrs):
  match found:
    case Some{Cli.EnvValue{name, +value}}:
      rev_pg(Cli.value_issue(kind, attrs, value), id, u, s, l, kind, attrs,
        name, value, okl, {==})
    case None{}:
      rd_pg(Cli.find_default(attrs), id, u, s, l, kind, attrs, okd, okl, {==})

def rag_seen(seen: Bool, +values: List<&2, String>, -count: Nat, +id: String,
    -u: String, -s: String, -l: String, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, h: Cli.Host,
    ok: {gib(kind, attrs, Cli.Gather{seen, values, count}) == True{} : Bool},
    okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    np: {Cli.kind_pos(kind) == False{} : Bool}) ->
    OW(Cli.resolve_argv_gather(Cli.Gather{seen, values, count},
      Cli.ArgInfo{id, u, s, l, kind, attrs}, h), id, kind, attrs):
  match seen:
    case True{}:
      one_ow(id, Cli.apply_delim(Cli.find_delim(attrs),
        List.reverse(&2, String, values)), Cli.Argv{}, kind, attrs,
        seen_good(kind, attrs, List.reverse(&2, String, values), count,
          rev_gib(kind, attrs, values, count, ok), okl, np))
    case False{}:
      red_pg(Cli.host_env(h, Cli.find_envs(attrs)), id, u, s, l, kind, attrs,
        okd, okl)

def rag_pg(g: Cli.Gather, +id: String, -u: String, -s: String, -l: String,
    +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>, h: Cli.Host,
    ok: {gib(kind, attrs, g) == True{} : Bool},
    okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    np: {Cli.kind_pos(kind) == False{} : Bool}) ->
    OW(Cli.resolve_argv_gather(g, Cli.ArgInfo{id, u, s, l, kind, attrs}, h),
      id, kind, attrs):
  match g:
    case Cli.Gather{seen, values, count}:
      rag_seen(seen, values, count, id, u, s, l, kind, attrs, h, ok, okd, okl,
        np)

# An option of id, which every event accepts, builds a field fgood accepts.
def opt_pg(+events: List<&2, Cli.ScanEvent>, +id: String, -u: String,
    -s: String, -l: String, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    h: Cli.Host, ev: {evs_ok(events, kind, attrs, id) == True{} : Bool},
    okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    np: {Cli.kind_pos(kind) == False{} : Bool}) ->
    OW(Cli.resolve_option(Cli.ArgInfo{id, u, s, l, kind, attrs}, events, h),
      id, kind, attrs):
  rag_pg(Cli.gather_events(events, id, kind, Cli.Gather{False{}, [], 0n}), id,
    u, s, l, kind, attrs, h, gather_all(events, id, kind, attrs,
      Cli.Gather{False{}, [], 0n}, gather_init(kind, attrs), ev), okd, okl, np)

def pos_fgood(-req: Bool, +many: Bool, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>,
    e: {Cli.first_bad(values, attrs) == None{} : Maybe<&2, Cli.Bad>},
    one: {Bool.or(many, Laws.read_most_one(values)) == True{} : Bool},
    ne: {Bool.or(many, Bool.not(List.is_empty(&2, String, values))) == True{}
      : Bool}) ->
    {fgood(Cli.PosKind{req, many}, attrs, values) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Cli.Bad>, Cli.first_bad(values, attrs), None{}, e) :
    {Bool.and(Bool.and(no_bad(_), Bool.or(many, Laws.read_most_one(values))),
      Bool.or(many, Bool.not(List.is_empty(&2, String, values)))) == True{}
      : Bool}
  and_true(Bool.or(many, Laws.read_most_one(values)),
    Bool.or(many, Bool.not(List.is_empty(&2, String, values))), one, ne)

def pvr_pg(found: Maybe<&2, Cli.Bad>, +id: String, -u: String, -s: String,
    -l: String, -req: Bool, +many: Bool, +attrs: List<&2, Cli.Item>,
    +values: List<&2, String>,
    e: {Cli.first_bad(values, attrs) == found : Maybe<&2, Cli.Bad>},
    one: {Bool.or(many, Laws.read_most_one(values)) == True{} : Bool},
    ne: {Bool.or(many, Bool.not(List.is_empty(&2, String, values))) == True{}
      : Bool}) ->
    OW(Cli.pos_valid_result(found, Cli.ArgInfo{id, u, s, l,
      Cli.PosKind{req, many}, attrs}, values), id, Cli.PosKind{req, many},
      attrs):
  match found:
    case Some{Cli.Bad{bad, why}}: Unit{}
    case None{}:
      one_ow(id, values, Cli.Argv{}, Cli.PosKind{req, many}, attrs,
        pos_fgood(req, many, attrs, values, e, one, ne))

def take_zero(xs: List<&2, String>) ->
    {List.is_empty(&2, String, List.take(&2, String, xs, 0n)) == True{}
      : Bool}:
  match xs:
    case Nil{}: {==}
    case h <> t: {==}

# A list positional's values, whichever the argv gives it.
def pos_vals(values: List<&2, String>, +id: String, -u: String, -s: String,
    -l: String, req: Bool, +attrs: List<&2, Cli.Item>, h: Cli.Host,
    okd: DefaultOk(Cli.find_default(attrs), Cli.PosKind{req, True{}}, attrs),
    okl: DelimOk(Cli.find_delim(attrs), Cli.PosKind{req, True{}})) ->
    OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, Cli.PosKind{req, True{}},
      attrs}, values, h), id, Cli.PosKind{req, True{}}, attrs):
  match values:
    case Nil{}:
      red_pg(Cli.host_env(h, Cli.find_envs(attrs)), id, u, s, l,
        Cli.PosKind{req, True{}}, attrs, okd, okl)
    case +v <> +vs:
      pvr_pg(Cli.first_bad(Cli.apply_delim(Cli.find_delim(attrs), v <> vs),
        attrs), id, u, s, l, req, True{}, attrs,
        Cli.apply_delim(Cli.find_delim(attrs), v <> vs), {==}, {==}, {==})

# A single positional takes one token, which no delim splits.
def sp_pg(fd: Maybe<&2, Char>, +id: String, -u: String, -s: String,
    -l: String, -req: Bool, +attrs: List<&2, Cli.Item>, +t: String,
    +ts: List<&2, String>, okl: DelimOk(fd, Cli.PosKind{req, False{}})) ->
    OW(Cli.pos_valid_result(Cli.first_bad(Cli.apply_delim(fd,
      t <> List.take(&2, String, ts, 0n)), attrs), Cli.ArgInfo{id, u, s, l,
      Cli.PosKind{req, False{}}, attrs}, Cli.apply_delim(fd,
      t <> List.take(&2, String, ts, 0n))), id, Cli.PosKind{req, False{}},
      attrs):
  match fd:
    case None{}:
      pvr_pg(Cli.first_bad(t <> List.take(&2, String, ts, 0n), attrs), id, u,
        s, l, req, False{}, attrs, t <> List.take(&2, String, ts, 0n), {==},
        take_zero(ts), {==})
    case Some{c}:
      Empty.absurd(OW(Cli.pos_valid_result(Cli.first_bad(Cli.apply_delim(
        Some{c}, t <> List.take(&2, String, ts, 0n)), attrs),
        Cli.ArgInfo{id, u, s, l, Cli.PosKind{req, False{}}, attrs},
        Cli.apply_delim(Some{c}, t <> List.take(&2, String, ts, 0n))), id,
        Cli.PosKind{req, False{}}, attrs), false_true_absurd(okl))

def pos_one(toks: List<&2, String>, +id: String, -u: String, -s: String,
    -l: String, req: Bool, +attrs: List<&2, Cli.Item>, h: Cli.Host,
    okd: DefaultOk(Cli.find_default(attrs), Cli.PosKind{req, False{}}, attrs),
    okl: DelimOk(Cli.find_delim(attrs), Cli.PosKind{req, False{}})) ->
    OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, Cli.PosKind{req, False{}},
      attrs}, List.take(&2, String, toks, Bool.pick(Nat,
      List.is_empty(&2, String, toks), 0n, 1n)), h), id,
      Cli.PosKind{req, False{}}, attrs):
  match toks:
    case Nil{}:
      red_pg(Cli.host_env(h, Cli.find_envs(attrs)), id, u, s, l,
        Cli.PosKind{req, False{}}, attrs, okd, okl)
    case t <> ts: sp_pg(Cli.find_delim(attrs), id, u, s, l, req, attrs, t, ts, okl)

def pos_many(many: Bool, +id: String, -u: String, -s: String, -l: String,
    req: Bool, +attrs: List<&2, Cli.Item>, h: Cli.Host,
    +toks: List<&2, String>, after: List<&2, Cli.ArgInfo>,
    okd: DefaultOk(Cli.find_default(attrs), Cli.PosKind{req, many}, attrs),
    okl: DelimOk(Cli.find_delim(attrs), Cli.PosKind{req, many})) ->
    OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, Cli.PosKind{req, many},
      attrs}, List.take(&2, String, toks, Cli.position_take_count(
      Cli.PosKind{req, many}, after, toks)), h), id, Cli.PosKind{req, many},
      attrs):
  match many:
    case True{}:
      pos_vals(List.take(&2, String, toks, Nat.sub(List.length(&2, String,
        toks), List.length(&2, Cli.ArgInfo, after))), id, u, s, l, req, attrs,
        h, okd, okl)
    case False{}: pos_one(toks, id, u, s, l, req, attrs, h, okd, okl)

# A positional of id builds a field fgood accepts from the tokens it takes.
def pos_pg(kind: Cli.UsageKind, +id: String, -u: String, -s: String,
    -l: String, +attrs: List<&2, Cli.Item>, h: Cli.Host,
    +toks: List<&2, String>, after: List<&2, Cli.ArgInfo>,
    okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    ep: {Cli.kind_pos(kind) == True{} : Bool}) ->
    OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, kind, attrs},
      List.take(&2, String, toks, Cli.position_take_count(kind, after, toks)),
      h), id, kind, attrs):
  match kind:
    case Cli.PosKind{req, many}:
      pos_many(many, id, u, s, l, req, attrs, h, toks, after, okd, okl)
    case Cli.FlagKind{}: Empty.absurd(OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, Cli.FlagKind{}, attrs}, List.take(&2, String, toks, Cli.position_take_count(Cli.FlagKind{}, after, toks)), h), id, Cli.FlagKind{}, attrs), false_true_absurd(ep))
    case Cli.CountKind{}: Empty.absurd(OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, Cli.CountKind{}, attrs}, List.take(&2, String, toks, Cli.position_take_count(Cli.CountKind{}, after, toks)), h), id, Cli.CountKind{}, attrs), false_true_absurd(ep))
    case Cli.NegatableKind{}: Empty.absurd(OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, Cli.NegatableKind{}, attrs}, List.take(&2, String, toks, Cli.position_take_count(Cli.NegatableKind{}, after, toks)), h), id, Cli.NegatableKind{}, attrs), false_true_absurd(ep))
    case Cli.OptionKind{x0}: Empty.absurd(OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, Cli.OptionKind{x0}, attrs}, List.take(&2, String, toks, Cli.position_take_count(Cli.OptionKind{x0}, after, toks)), h), id, Cli.OptionKind{x0}, attrs), false_true_absurd(ep))
    case Cli.BareOptionKind{}: Empty.absurd(OW(Cli.resolve_pos(Cli.ArgInfo{id, u, s, l, Cli.BareOptionKind{}, attrs}, List.take(&2, String, toks, Cli.position_take_count(Cli.BareOptionKind{}, after, toks)), h), id, Cli.BareOptionKind{}, attrs), false_true_absurd(ep))

# The arg arg_ref finds has id.
def ref_key_pick(c: Bool, -info: Cli.ArgInfo, -rest: Maybe<&2, Cli.ArgInfo>,
    +id: String, -r: Cli.ArgInfo,
    ec: {String.eq(Cli.info_id(info), id) == c : Bool},
    er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info}, rest) == Some{r}
      : Maybe<&2, Cli.ArgInfo>},
    ih: {rest == Some{r} : Maybe<&2, Cli.ArgInfo>} ->
      {String.eq(Cli.info_id(r), id) == True{} : Bool}) ->
    {String.eq(Cli.info_id(r), id) == True{} : Bool}:
  match c:
    case True{}:
      %some_inj(info, r, er) :
        {String.eq(Cli.info_id(_), id) == True{} : Bool}
      ec
    case False{}: ih(er)

def ref_key(L: List<&2, Cli.Item>, +id: String, -r: Cli.ArgInfo,
    er: {Laws.arg_ref(L, id) == Some{r} : Maybe<&2, Cli.ArgInfo>}) ->
    {String.eq(Cli.info_id(r), id) == True{} : Bool}:
  match L:
    case Nil{}:
      Empty.absurd({String.eq(Cli.info_id(r), id) == True{} : Bool},
        arg_none_some(r, er))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      ref_key_pick(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), Laws.arg_ref(tail, id), id, r, {==}, er,
        et => ref_key(tail, id, r, et))
    case Cli.Sub{x0, x1, x2} <> tail: ref_key(tail, id, r, er)
    case Cli.Version{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Alias{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Hidden{} <> tail: ref_key(tail, id, r, er)
    case Cli.Example{x0, x1} <> tail: ref_key(tail, id, r, er)
    case Cli.After{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.SubOptional{} <> tail: ref_key(tail, id, r, er)
    case Cli.External{} <> tail: ref_key(tail, id, r, er)
    case Cli.Exclusive{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.NeedOne{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Id{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Required{} <> tail: ref_key(tail, id, r, er)
    case Cli.AttrDefault{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.AttrEnv{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Global{} <> tail: ref_key(tail, id, r, er)
    case Cli.Heading{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.As{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.OneOf{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Delim{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Hyphen{} <> tail: ref_key(tail, id, r, er)
    case Cli.Rest{} <> tail: ref_key(tail, id, r, er)
    case Cli.Bare{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Conflicts{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Requires{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Group{x0} <> tail: ref_key(tail, id, r, er)
    case Cli.Builtin{} <> tail: ref_key(tail, id, r, er)

def ref_np_pick(c: Bool, info: Cli.ArgInfo, -rest: Maybe<&2, Cli.ArgInfo>,
    -r: Cli.ArgInfo,
    er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info}, rest) == Some{r}
      : Maybe<&2, Cli.ArgInfo>},
    np: {Bool.not(Cli.kind_pos(Cli.info_kind(info))) == True{} : Bool},
    ih: {rest == Some{r} : Maybe<&2, Cli.ArgInfo>} ->
      {Cli.kind_pos(Cli.info_kind(r)) == False{} : Bool}) ->
    {Cli.kind_pos(Cli.info_kind(r)) == False{} : Bool}:
  match c:
    case True{}:
      %some_inj(info, r, er) :
        {Cli.kind_pos(Cli.info_kind(_)) == False{} : Bool}
      nt_f(Cli.kind_pos(Cli.info_kind(info)), np)
    case False{}: ih(er)

# An arg arg_ref finds in a list with no positional is not positional.
def ref_np(L: List<&2, Cli.Item>, +id: String, -r: Cli.ArgInfo,
    er: {Laws.arg_ref(L, id) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    +np: {nonpos(L) == True{} : Bool}) ->
    {Cli.kind_pos(Cli.info_kind(r)) == False{} : Bool}:
  match L:
    case Nil{}:
      Empty.absurd({Cli.kind_pos(Cli.info_kind(r)) == False{} : Bool},
        arg_none_some(r, er))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      ref_np_pick(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), Laws.arg_ref(tail, id), r, er,
        and_left(Bool.not(Cli.kind_pos(Cli.info_kind(Cli.arg_info(usage,
          attrs)))), nonpos(tail), np),
        et => ref_np(tail, id, r, et, and_right(Bool.not(Cli.kind_pos(
          Cli.info_kind(Cli.arg_info(usage, attrs)))), nonpos(tail), np)))
    case Cli.Sub{x0, x1, x2} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Version{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Alias{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Hidden{} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Example{x0, x1} <> tail: ref_np(tail, id, r, er, np)
    case Cli.After{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.SubOptional{} <> tail: ref_np(tail, id, r, er, np)
    case Cli.External{} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Exclusive{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.NeedOne{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Id{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Required{} <> tail: ref_np(tail, id, r, er, np)
    case Cli.AttrDefault{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.AttrEnv{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Global{} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Heading{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.As{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.OneOf{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Delim{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Hyphen{} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Rest{} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Bare{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Conflicts{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Requires{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Group{x0} <> tail: ref_np(tail, id, r, er, np)
    case Cli.Builtin{} <> tail: ref_np(tail, id, r, er, np)

# The arg of id, when there is one, is positional (PM) or not (NPm).
def PM(m: Maybe<&2, Cli.ArgInfo>) -> Type:
  match m:
    case None{}: Unit
    case Some{x}: {Cli.kind_pos(Cli.info_kind(x)) == True{} : Bool}

def NPm(m: Maybe<&2, Cli.ArgInfo>) -> Type:
  match m:
    case None{}: Unit
    case Some{x}: {Cli.kind_pos(Cli.info_kind(x)) == False{} : Bool}

def on_kp(kp: Bool, +info: Cli.ArgInfo, +events: List<&2, Cli.ScanEvent>,
    +h: Cli.Host, later: Cli.FieldBuild, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool},
    nl: NK(later, id)) ->
    NK(Cli.resolve_arg(kp, info, events, h, later), id):
  match kp:
    case True{}: nl
    case False{}:
      nk_comb(Cli.resolve_option(info, events, h), later, id,
        rf_nk(info, events, h, id, ec), nl)

def on_t(m: Maybe<&2, Cli.ArgInfo>, +info: Cli.ArgInfo,
    +tail: List<&2, Cli.Item>, +events: List<&2, Cli.ScanEvent>,
    +h: Cli.Host, +id: String,
    er: {Some{info} == m : Maybe<&2, Cli.ArgInfo>}, ep: PM(m),
    ht: {has(tail, id) == False{} : Bool},
    ih: @m2: Maybe<&2, Cli.ArgInfo> ->
      {Laws.arg_ref(tail, id) == m2 : Maybe<&2, Cli.ArgInfo>} -> PM(m2) ->
      NK(Cli.resolve_options(Cli.spec_items(tail), events, h), id)) ->
    NK(Cli.resolve_arg(Cli.kind_pos(Cli.info_kind(info)), info, events, h,
      Cli.resolve_options(Cli.spec_items(tail), events, h)), id):
  match m:
    case None{}:
      Empty.absurd(NK(Cli.resolve_arg(Cli.kind_pos(Cli.info_kind(info)), info,
        events, h, Cli.resolve_options(Cli.spec_items(tail), events, h)), id),
        some_none_absurd(info, er))
    case Some{r}:
      %Equal.sym(Bool, Cli.kind_pos(Cli.info_kind(info)), True{},
        (%Equal.sym(Cli.ArgInfo, info, r, some_inj(info, r, er)) :
          {Cli.kind_pos(Cli.info_kind(_)) == True{} : Bool}
        ep)) :
        NK(Cli.resolve_arg(_, info, events, h,
          Cli.resolve_options(Cli.spec_items(tail), events, h)), id)
      ih(None{}, ref_none(tail, id, ht), Unit{})

def on_c(c: Bool, m: Maybe<&2, Cli.ArgInfo>, +info: Cli.ArgInfo,
    +tail: List<&2, Cli.Item>, +events: List<&2, Cli.ScanEvent>,
    +h: Cli.Host, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == c : Bool},
    er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info},
      Laws.arg_ref(tail, id)) == m : Maybe<&2, Cli.ArgInfo>},
    ep: PM(m),
    am: {Bool.and(Bool.or(Bool.not(c), Bool.not(has(tail, id))),
      am1(tail, id)) == True{} : Bool},
    ih: @m2: Maybe<&2, Cli.ArgInfo> ->
      {Laws.arg_ref(tail, id) == m2 : Maybe<&2, Cli.ArgInfo>} -> PM(m2) ->
      NK(Cli.resolve_options(Cli.spec_items(tail), events, h), id)) ->
    NK(Cli.resolve_arg(Cli.kind_pos(Cli.info_kind(info)), info, events, h,
      Cli.resolve_options(Cli.spec_items(tail), events, h)), id):
  match c:
    case True{}:
      on_t(m, info, tail, events, h, id, er, ep,
        nt_f(has(tail, id), and_left(Bool.not(has(tail, id)), am1(tail, id),
          am)), ih)
    case False{}:
      on_kp(Cli.kind_pos(Cli.info_kind(info)), info, events, h,
        Cli.resolve_options(Cli.spec_items(tail), events, h), id, ec,
        ih(m, er, ep))

# Options with no non-positional arg of id build no field of id.
def on(X: List<&2, Cli.Item>, +events: List<&2, Cli.ScanEvent>, +h: Cli.Host,
    +id: String, m: Maybe<&2, Cli.ArgInfo>,
    er: {Laws.arg_ref(X, id) == m : Maybe<&2, Cli.ArgInfo>}, ep: PM(m),
    +am: {am1(X, id) == True{} : Bool}) ->
    NK(Cli.resolve_options(Cli.spec_items(X), events, h), id):
  match X:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      on_c(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id), m,
        Cli.arg_info(usage, attrs), tail, events, h, id, {==}, er, ep, am,
        m2 => e2 => p2 => on(tail, events, h, id, m2, e2, p2,
          and_right(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(
            usage, attrs)), id)), Bool.not(has(tail, id))), am1(tail, id),
            am)))
    case Cli.Sub{x0, x1, x2} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Version{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Alias{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Hidden{} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Example{x0, x1} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.After{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.SubOptional{} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.External{} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Exclusive{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.NeedOne{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Id{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Required{} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.AttrDefault{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.AttrEnv{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Global{} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Heading{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.As{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.OneOf{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Delim{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Hyphen{} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Rest{} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Bare{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Conflicts{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Requires{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Group{x0} <> tail: on(tail, events, h, id, m, er, ep, am)
    case Cli.Builtin{} <> tail: on(tail, events, h, id, m, er, ep, am)

def oa_kp(kp: Bool, +info: Cli.ArgInfo, +events: List<&2, Cli.ScanEvent>,
    +h: Cli.Host, later: Cli.FieldBuild, +id: String, -kind: Cli.UsageKind,
    -attrs: List<&2, Cli.Item>,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool},
    ol: OW(later, id, kind, attrs)) ->
    OW(Cli.resolve_arg(kp, info, events, h, later), id, kind, attrs):
  match kp:
    case True{}: ol
    case False{}:
      nk_ow(Cli.resolve_option(info, events, h), later, id, kind, attrs,
        rf_nk(info, events, h, id, ec), ol)

def oa_c(c: Bool, +info: Cli.ArgInfo, +tail: List<&2, Cli.Item>,
    +events: List<&2, Cli.ScanEvent>, +h: Cli.Host, +id: String,
    -r: Cli.ArgInfo, ec: {String.eq(Cli.info_id(info), id) == c : Bool},
    +er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info},
      Laws.arg_ref(tail, id)) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    enp: {Cli.kind_pos(Cli.info_kind(r)) == False{} : Bool},
    pg: OW(Cli.resolve_option(r, events, h), id, Cli.info_kind(r),
      Cli.info_attrs(r)),
    +am: {Bool.and(Bool.or(Bool.not(c), Bool.not(has(tail, id))),
      am1(tail, id)) == True{} : Bool},
    ih: OW(Cli.resolve_option(r, events, h), id, Cli.info_kind(r),
      Cli.info_attrs(r)) ->
      {Laws.arg_ref(tail, id) == Some{r} : Maybe<&2, Cli.ArgInfo>} ->
      OW(Cli.resolve_options(Cli.spec_items(tail), events, h), id,
        Cli.info_kind(r), Cli.info_attrs(r))) ->
    OW(Cli.resolve_arg(Cli.kind_pos(Cli.info_kind(info)), info, events, h,
      Cli.resolve_options(Cli.spec_items(tail), events, h)), id,
      Cli.info_kind(r), Cli.info_attrs(r)):
  match c:
    case True{}:
      +ei = Equal.sym(Cli.ArgInfo, info, r, some_inj(info, r, er))
      %Equal.sym(Bool, Cli.kind_pos(Cli.info_kind(info)), False{},
        (%ei : {Cli.kind_pos(Cli.info_kind(_)) == False{} : Bool}
        enp)) :
        OW(Cli.resolve_arg(_, info, events, h,
          Cli.resolve_options(Cli.spec_items(tail), events, h)), id,
          Cli.info_kind(r), Cli.info_attrs(r))
      ow_nk(Cli.resolve_option(info, events, h),
        Cli.resolve_options(Cli.spec_items(tail), events, h), id,
        Cli.info_kind(r), Cli.info_attrs(r),
        (%ei : OW(Cli.resolve_option(_, events, h), id, Cli.info_kind(r),
          Cli.info_attrs(r))
        pg),
        on(tail, events, h, id, None{}, ref_none(tail, id,
          nt_f(has(tail, id), and_left(Bool.not(has(tail, id)),
            am1(tail, id), am))), Unit{},
          and_right(Bool.not(has(tail, id)), am1(tail, id), am)))
    case False{}:
      oa_kp(Cli.kind_pos(Cli.info_kind(info)), info, events, h,
        Cli.resolve_options(Cli.spec_items(tail), events, h), id,
        Cli.info_kind(r), Cli.info_attrs(r), ec, ih(pg, er))

# Options holding a non-positional arg r of id build r's field.
def oa(X: List<&2, Cli.Item>, +events: List<&2, Cli.ScanEvent>, +h: Cli.Host,
    +id: String, -r: Cli.ArgInfo,
    er: {Laws.arg_ref(X, id) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    +enp: {Cli.kind_pos(Cli.info_kind(r)) == False{} : Bool},
    pg: OW(Cli.resolve_option(r, events, h), id, Cli.info_kind(r),
      Cli.info_attrs(r)),
    +am: {am1(X, id) == True{} : Bool}) ->
    OW(Cli.resolve_options(Cli.spec_items(X), events, h), id,
      Cli.info_kind(r), Cli.info_attrs(r)):
  match X:
    case Nil{}:
      Empty.absurd(OW(Cli.Built{[]}, id, Cli.info_kind(r), Cli.info_attrs(r)),
        arg_none_some(r, er))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      oa_c(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), tail, events, h, id, r, {==}, er, enp, pg,
        am, p2 => et => oa(tail, events, h, id, r, et, enp, p2,
          and_right(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(
            usage, attrs)), id)), Bool.not(has(tail, id))), am1(tail, id),
            am)))
    case Cli.Sub{x0, x1, x2} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Version{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Alias{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Hidden{} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Example{x0, x1} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.After{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.SubOptional{} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.External{} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Exclusive{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.NeedOne{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Id{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Required{} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.AttrDefault{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.AttrEnv{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Global{} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Heading{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.As{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.OneOf{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Delim{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Hyphen{} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Rest{} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Bare{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Conflicts{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Requires{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Group{x0} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)
    case Cli.Builtin{} <> tail: oa(tail, events, h, id, r, er, enp, pg, am)

def pn_kp(kp: Bool, +info: Cli.ArgInfo, +tail: List<&2, Cli.ArgInfo>,
    +toks: List<&2, String>, +h: Cli.Host, +id: String,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool},
    ih: @t: List<&2, String> -> NK(Cli.resolve_positions(tail, t, h), id)) ->
    NK(Cli.resolve_positions(Bool.pick(List<&2, Cli.ArgInfo>, kp,
      info <> tail, tail), toks, h), id):
  match kp:
    case True{}:
      +n = Cli.position_take_count(Cli.info_kind(info), tail, toks)
      nk_comb(Cli.resolve_pos(info, List.take(&2, String, toks, n), h),
        Cli.resolve_positions(tail, List.drop(&2, String, toks, n), h), id,
        rp_nk(info, List.take(&2, String, toks, n), h, id, ec),
        ih(List.drop(&2, String, toks, n)))
    case False{}: ih(toks)

def pn_t(m: Maybe<&2, Cli.ArgInfo>, +info: Cli.ArgInfo,
    +tail: List<&2, Cli.Item>, +toks: List<&2, String>, +h: Cli.Host,
    +id: String, er: {Some{info} == m : Maybe<&2, Cli.ArgInfo>}, np: NPm(m),
    ht: {has(tail, id) == False{} : Bool},
    ih: @t: List<&2, String> -> @m2: Maybe<&2, Cli.ArgInfo> ->
      {Laws.arg_ref(tail, id) == m2 : Maybe<&2, Cli.ArgInfo>} -> NPm(m2) ->
      NK(Cli.resolve_positions(Cli.spec_slots(Cli.spec_items(tail)), t, h),
        id)) ->
    NK(Cli.resolve_positions(Bool.pick(List<&2, Cli.ArgInfo>,
      Cli.kind_pos(Cli.info_kind(info)),
      info <> Cli.spec_slots(Cli.spec_items(tail)),
      Cli.spec_slots(Cli.spec_items(tail))), toks, h), id):
  match m:
    case None{}:
      Empty.absurd(NK(Cli.resolve_positions(Bool.pick(List<&2, Cli.ArgInfo>,
        Cli.kind_pos(Cli.info_kind(info)),
        info <> Cli.spec_slots(Cli.spec_items(tail)),
        Cli.spec_slots(Cli.spec_items(tail))), toks, h), id),
        some_none_absurd(info, er))
    case Some{r}:
      %Equal.sym(Bool, Cli.kind_pos(Cli.info_kind(info)), False{},
        (%Equal.sym(Cli.ArgInfo, info, r, some_inj(info, r, er)) :
          {Cli.kind_pos(Cli.info_kind(_)) == False{} : Bool}
        np)) :
        NK(Cli.resolve_positions(Bool.pick(List<&2, Cli.ArgInfo>, _,
          info <> Cli.spec_slots(Cli.spec_items(tail)),
          Cli.spec_slots(Cli.spec_items(tail))), toks, h), id)
      ih(toks, None{}, ref_none(tail, id, ht), Unit{})

def pn_c(c: Bool, m: Maybe<&2, Cli.ArgInfo>, +info: Cli.ArgInfo,
    +tail: List<&2, Cli.Item>, +toks: List<&2, String>, +h: Cli.Host,
    +id: String, ec: {String.eq(Cli.info_id(info), id) == c : Bool},
    er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info},
      Laws.arg_ref(tail, id)) == m : Maybe<&2, Cli.ArgInfo>},
    np: NPm(m),
    am: {Bool.and(Bool.or(Bool.not(c), Bool.not(has(tail, id))),
      am1(tail, id)) == True{} : Bool},
    ih: @t: List<&2, String> -> @m2: Maybe<&2, Cli.ArgInfo> ->
      {Laws.arg_ref(tail, id) == m2 : Maybe<&2, Cli.ArgInfo>} -> NPm(m2) ->
      NK(Cli.resolve_positions(Cli.spec_slots(Cli.spec_items(tail)), t, h),
        id)) ->
    NK(Cli.resolve_positions(Bool.pick(List<&2, Cli.ArgInfo>,
      Cli.kind_pos(Cli.info_kind(info)),
      info <> Cli.spec_slots(Cli.spec_items(tail)),
      Cli.spec_slots(Cli.spec_items(tail))), toks, h), id):
  match c:
    case True{}:
      pn_t(m, info, tail, toks, h, id, er, np,
        nt_f(has(tail, id), and_left(Bool.not(has(tail, id)), am1(tail, id),
          am)), ih)
    case False{}:
      pn_kp(Cli.kind_pos(Cli.info_kind(info)), info,
        Cli.spec_slots(Cli.spec_items(tail)), toks, h, id, ec,
        t => ih(t, m, er, np))

# Positionals with no positional arg of id build no field of id.
def pn(I: List<&2, Cli.Item>, +toks: List<&2, String>, +h: Cli.Host,
    +id: String, m: Maybe<&2, Cli.ArgInfo>,
    er: {Laws.arg_ref(I, id) == m : Maybe<&2, Cli.ArgInfo>}, np: NPm(m),
    +am: {am1(I, id) == True{} : Bool}) ->
    NK(Cli.resolve_positions(Cli.spec_slots(Cli.spec_items(I)), toks, h), id):
  match I:
    case Nil{}: {==}
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      pn_c(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id), m,
        Cli.arg_info(usage, attrs), tail, toks, h, id, {==}, er, np, am,
        t => m2 => e2 => p2 => pn(tail, t, h, id, m2, e2, p2,
          and_right(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(
            usage, attrs)), id)), Bool.not(has(tail, id))), am1(tail, id),
            am)))
    case Cli.Sub{x0, x1, x2} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Version{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Alias{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Hidden{} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Example{x0, x1} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.After{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.SubOptional{} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.External{} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Exclusive{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.NeedOne{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Id{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Required{} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.AttrDefault{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.AttrEnv{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Global{} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Heading{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.As{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.OneOf{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Delim{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Hyphen{} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Rest{} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Bare{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Conflicts{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Requires{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Group{x0} <> tail: pn(tail, toks, h, id, m, er, np, am)
    case Cli.Builtin{} <> tail: pn(tail, toks, h, id, m, er, np, am)

# What a positional r builds from any tokens it takes before after's.
def PPG(r: Cli.ArgInfo, h: Cli.Host, id: String) -> Type:
  @toks: List<&2, String> -> @after: List<&2, Cli.ArgInfo> ->
    OW(Cli.resolve_pos(r, List.take(&2, String, toks,
      Cli.position_take_count(Cli.info_kind(r), after, toks)), h), id,
      Cli.info_kind(r), Cli.info_attrs(r))

def pi_kp(kp: Bool, +info: Cli.ArgInfo, +tail: List<&2, Cli.ArgInfo>,
    +toks: List<&2, String>, +h: Cli.Host, +id: String,
    -kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>,
    ec: {String.eq(Cli.info_id(info), id) == False{} : Bool},
    ih: @t: List<&2, String> ->
      OW(Cli.resolve_positions(tail, t, h), id, kind, attrs)) ->
    OW(Cli.resolve_positions(Bool.pick(List<&2, Cli.ArgInfo>, kp,
      info <> tail, tail), toks, h), id, kind, attrs):
  match kp:
    case True{}:
      +n = Cli.position_take_count(Cli.info_kind(info), tail, toks)
      nk_ow(Cli.resolve_pos(info, List.take(&2, String, toks, n), h),
        Cli.resolve_positions(tail, List.drop(&2, String, toks, n), h), id,
        kind, attrs, rp_nk(info, List.take(&2, String, toks, n), h, id, ec),
        ih(List.drop(&2, String, toks, n)))
    case False{}: ih(toks)

def pi_c(c: Bool, +info: Cli.ArgInfo, +tail: List<&2, Cli.Item>,
    +toks: List<&2, String>, +h: Cli.Host, +id: String, -r: Cli.ArgInfo,
    ec: {String.eq(Cli.info_id(info), id) == c : Bool},
    +er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info},
      Laws.arg_ref(tail, id)) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    ep: {Cli.kind_pos(Cli.info_kind(r)) == True{} : Bool},
    ppg: PPG(r, h, id),
    +am: {Bool.and(Bool.or(Bool.not(c), Bool.not(has(tail, id))),
      am1(tail, id)) == True{} : Bool},
    ih: PPG(r, h, id) ->
      {Laws.arg_ref(tail, id) == Some{r} : Maybe<&2, Cli.ArgInfo>} ->
      @t: List<&2, String> ->
      OW(Cli.resolve_positions(Cli.spec_slots(Cli.spec_items(tail)), t, h),
        id, Cli.info_kind(r), Cli.info_attrs(r))) ->
    OW(Cli.resolve_positions(Bool.pick(List<&2, Cli.ArgInfo>,
      Cli.kind_pos(Cli.info_kind(info)),
      info <> Cli.spec_slots(Cli.spec_items(tail)),
      Cli.spec_slots(Cli.spec_items(tail))), toks, h), id, Cli.info_kind(r),
      Cli.info_attrs(r)):
  match c:
    case True{}:
      +ei = Equal.sym(Cli.ArgInfo, info, r, some_inj(info, r, er))
      +rest = Cli.spec_slots(Cli.spec_items(tail))
      +n = Cli.position_take_count(Cli.info_kind(info), rest, toks)
      %Equal.sym(Bool, Cli.kind_pos(Cli.info_kind(info)), True{},
        (%ei : {Cli.kind_pos(Cli.info_kind(_)) == True{} : Bool}
        ep)) :
        OW(Cli.resolve_positions(Bool.pick(List<&2, Cli.ArgInfo>, _,
          info <> rest, rest), toks, h), id, Cli.info_kind(r),
          Cli.info_attrs(r))
      ow_nk(Cli.resolve_pos(info, List.take(&2, String, toks, n), h),
        Cli.resolve_positions(rest, List.drop(&2, String, toks, n), h), id,
        Cli.info_kind(r), Cli.info_attrs(r),
        (%ei : OW(Cli.resolve_pos(_, List.take(&2, String, toks,
          Cli.position_take_count(Cli.info_kind(_), rest, toks)), h), id,
          Cli.info_kind(r), Cli.info_attrs(r))
        ppg(toks, rest)),
        pn(tail, List.drop(&2, String, toks, n), h, id, None{},
          ref_none(tail, id, nt_f(has(tail, id), and_left(
            Bool.not(has(tail, id)), am1(tail, id), am))), Unit{},
          and_right(Bool.not(has(tail, id)), am1(tail, id), am)))
    case False{}:
      pi_kp(Cli.kind_pos(Cli.info_kind(info)), info,
        Cli.spec_slots(Cli.spec_items(tail)), toks, h, id, Cli.info_kind(r),
        Cli.info_attrs(r), ec, ih(ppg, er))

# Positionals holding a positional arg r of id build r's field.
def pi(I: List<&2, Cli.Item>, +toks: List<&2, String>, +h: Cli.Host,
    +id: String, -r: Cli.ArgInfo,
    er: {Laws.arg_ref(I, id) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    +ep: {Cli.kind_pos(Cli.info_kind(r)) == True{} : Bool},
    ppg: PPG(r, h, id), +am: {am1(I, id) == True{} : Bool}) ->
    OW(Cli.resolve_positions(Cli.spec_slots(Cli.spec_items(I)), toks, h), id,
      Cli.info_kind(r), Cli.info_attrs(r)):
  match I:
    case Nil{}:
      Empty.absurd(OW(Cli.Built{[]}, id, Cli.info_kind(r), Cli.info_attrs(r)),
        arg_none_some(r, er))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      pi_c(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), tail, toks, h, id, r, {==}, er, ep, ppg,
        am, p2 => et => t => pi(tail, t, h, id, r, et, ep, p2,
          and_right(Bool.or(Bool.not(String.eq(Cli.info_id(Cli.arg_info(
            usage, attrs)), id)), Bool.not(has(tail, id))), am1(tail, id),
            am)))
    case Cli.Sub{x0, x1, x2} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Version{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Alias{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Hidden{} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Example{x0, x1} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.After{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.SubOptional{} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.External{} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Exclusive{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.NeedOne{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Id{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Required{} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.AttrDefault{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.AttrEnv{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Global{} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Heading{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.As{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.OneOf{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Delim{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Hyphen{} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Rest{} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Bare{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Conflicts{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Requires{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Group{x0} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)
    case Cli.Builtin{} <> tail: pi(tail, toks, h, id, r, er, ep, ppg, am)

def slist_disc(l: List<&2, String>) -> Data:
  match l:
    case Nil{}: Empty
    case h <> t: Unit

def slist_cons_absurd(-h: String, -t: List<&2, String>,
    e: {h <> t == Nil{} : List<&2, String>}) -> Empty:
  %e : slist_disc(_)
  Unit{}

def sapp_nil_left(a: List<&2, String>, -b: List<&2, String>,
    e: {List.append(&2, String, a, b) == Nil{} : List<&2, String>}) ->
    {a == Nil{} : List<&2, String>}:
  match a:
    case Nil{}: {==}
    case h <> t:
      Empty.absurd({h <> t == Nil{} : List<&2, String>},
        slist_cons_absurd(h, List.append(&2, String, t, b), e))

def sapp_nil_right(a: List<&2, String>, -b: List<&2, String>,
    e: {List.append(&2, String, a, b) == Nil{} : List<&2, String>}) ->
    {b == Nil{} : List<&2, String>}:
  match a:
    case Nil{}: e
    case h <> t:
      Empty.absurd({b == Nil{} : List<&2, String>},
        slist_cons_absurd(h, List.append(&2, String, t, b), e))

def ma_off(arm: Bool, -d: String,
    e: {Bool.pick(List<&2, String>, arm, [d], []) == Nil{}
      : List<&2, String>}) -> {arm == False{} : Bool}:
  match arm:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, slist_cons_absurd(d, Nil{}, e))
    case False{}: {==}

def mi_c(c: Bool, +info: Cli.ArgInfo, +tail: List<&2, Cli.Item>,
    +all: List<&2, Cli.SpecItem>, +fields: List<&2, Cli.Field>,
    -done: List<&2, String>, +id: String, -r: Cli.ArgInfo,
    er: {Bool.pick(Maybe<&2, Cli.ArgInfo>, c, Some{info},
      Laws.arg_ref(tail, id)) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    em: {List.append(&2, String, Cli.missing_arg(info, fields),
      Cli.missing_items(Cli.spec_items(tail), all, fields, done)) == Nil{}
      : List<&2, String>},
    ih: {Laws.arg_ref(tail, id) == Some{r} : Maybe<&2, Cli.ArgInfo>} ->
      {Cli.missing_items(Cli.spec_items(tail), all, fields, done) == Nil{}
        : List<&2, String>} ->
      {Cli.arg_required_missing(r, fields) == False{} : Bool}) ->
    {Cli.arg_required_missing(r, fields) == False{} : Bool}:
  match c:
    case True{}:
      %some_inj(info, r, er) :
        {Cli.arg_required_missing(_, fields) == False{} : Bool}
      ma_off(Cli.arg_required_missing(info, fields), Cli.arg_display(info),
        sapp_nil_left(Cli.missing_arg(info, fields),
          Cli.missing_items(Cli.spec_items(tail), all, fields, done), em))
    case False{}:
      ih(er, sapp_nil_right(Cli.missing_arg(info, fields),
        Cli.missing_items(Cli.spec_items(tail), all, fields, done), em))

# Nothing missing leaves the arg of id, which arg_ref finds, not missing.
def mi_go(X: List<&2, Cli.Item>, +all: List<&2, Cli.SpecItem>,
    +fields: List<&2, Cli.Field>, +done: List<&2, String>, +id: String,
    -r: Cli.ArgInfo,
    er: {Laws.arg_ref(X, id) == Some{r} : Maybe<&2, Cli.ArgInfo>},
    em: {Cli.missing_items(Cli.spec_items(X), all, fields, done) == Nil{}
      : List<&2, String>}) ->
    {Cli.arg_required_missing(r, fields) == False{} : Bool}:
  match X:
    case Nil{}:
      Empty.absurd({Cli.arg_required_missing(r, fields) == False{} : Bool},
        arg_none_some(r, er))
    case Cli.Arg{+usage, help, +attrs} <> +tail:
      mi_c(String.eq(Cli.info_id(Cli.arg_info(usage, attrs)), id),
        Cli.arg_info(usage, attrs), tail, all, fields, done, id, r, er, em,
        et => ef => mi_go(tail, all, fields, done, id, r, et, ef))
    case Cli.NeedOne{+name} <> +tail:
      mi_go(tail, all, fields, name <> done, id, r, er, sapp_nil_right(
        Cli.missing_once(List.contains(~String, ~String.eq, done, name), all,
          fields, name),
        Cli.missing_items(Cli.spec_items(tail), all, fields, name <> done),
        em))
    case Cli.Sub{x0, x1, x2} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Version{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Alias{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Hidden{} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Example{x0, x1} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.After{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.SubOptional{} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.External{} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Exclusive{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Id{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Required{} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.AttrDefault{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.AttrEnv{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Global{} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Heading{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.As{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.OneOf{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Delim{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Hyphen{} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Rest{} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Bare{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Conflicts{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Requires{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Group{x0} <> tail: mi_go(tail, all, fields, done, id, r, er, em)
    case Cli.Builtin{} <> tail: mi_go(tail, all, fields, done, id, r, er, em)

def ap_off(m: Bool, hr: Bool, d: Bool, -kp: Bool,
    ehr: {hr == False{} : Bool}, ed: {d == False{} : Bool},
    ek: {kp == False{} : Bool}) ->
    {Bool.and(m, Bool.or(hr, Bool.or(d, kp))) == False{} : Bool}:
  match m:
    case True{}: b_or_ff(hr, Bool.or(d, kp), ehr, b_or_ff(d, kp, ed, ek))
    case False{}: {==}

def vs_nil(kind: Cli.UsageKind, -attrs: List<&2, Cli.Item>) ->
    {vs_ok(kind, attrs, Nil{}) == True{} : Bool}:
  match kind:
    case Cli.FlagKind{}: {==}
    case Cli.CountKind{}: {==}
    case Cli.NegatableKind{}: {==}
    case Cli.OptionKind{many}: or_true_right(many)
    case Cli.BareOptionKind{}: {==}
    case Cli.PosKind{required, many}: or_true_right(many)

# An absent field, which missing found not required, has no values and its
# arg no default, so it is no gap.
def absent_fin(vs: List<&2, String>, want: Cli.Want, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +id: String, fr: AbsentOk(vs, attrs),
    +arm: {Bool.or(Bool.and(Cli.has_required(attrs), True{}),
      Bool.and(Cli.kind_required_pos(kind), True{})) == False{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(want, id, kind, attrs), want, vs)
      == True{} : Bool}:
  match vs:
    case Nil{}:
      +hr = Cli.has_required(attrs)
      +kp = Cli.kind_required_pos(kind)
      final(want, kind, attrs, id, Nil{}, vs_nil(kind, attrs),
        ap_off(Bool.not(Cli.kind_many(kind)), hr,
          Maybe.is_some(&2, String, Cli.find_default(attrs)), kp,
          and_true_false(hr, b_orf_l(Bool.and(hr, True{}),
            Bool.and(kp, True{}), arm)),
          fr,
          and_true_false(kp, b_orf_r(Bool.and(hr, True{}),
            Bool.and(kp, True{}), arm))))
    case v <> t:
      Empty.absurd({Laws.read_at(Cli.want_verdict(want, id, kind, attrs),
        want, v <> t) == True{} : Bool}, fr)

def fin_good(want: Cli.Want, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +id: String, +vs: List<&2, String>,
    +fr: {fgood(kind, attrs, vs) == True{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(want, id, kind, attrs), want, vs)
      == True{} : Bool}:
  final(want, kind, attrs, id, vs, fgood_ok(kind, attrs, vs, fr),
    fgood_gap(kind, attrs, vs, fr))

def ffs(src: Cli.Src, want: Cli.Want, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +id: String, +vs: List<&2, String>,
    fr: FRs(src, kind, attrs, vs),
    arm: {Bool.or(Bool.and(Cli.has_required(attrs),
      Bool.not(Cli.source_given(src))), Bool.and(Cli.kind_required_pos(kind),
      Bool.not(Cli.source_present(src)))) == False{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(want, id, kind, attrs), want, vs)
      == True{} : Bool}:
  match src:
    case Cli.Argv{}: fin_good(want, kind, attrs, id, vs, fr)
    case Cli.Env{}: fin_good(want, kind, attrs, id, vs, fr)
    case Cli.Default{}: fin_good(want, kind, attrs, id, vs, fr)
    case Cli.Absent{}: absent_fin(vs, want, kind, attrs, id, fr, arm)

def ff(f: Cli.Field, want: Cli.Want, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>, +id: String, fr: FR(f, kind, attrs),
    arm: {Bool.or(Bool.and(Cli.has_required(attrs),
      Bool.not(Cli.source_given(fsrc(f)))), Bool.and(Cli.kind_required_pos(kind),
      Bool.not(Cli.source_present(fsrc(f))))) == False{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(want, id, kind, attrs), want,
      Cli.field_values(f)) == True{} : Bool}:
  match f:
    case Cli.Field{key, values, source}:
      ffs(source, want, kind, attrs, id, values, fr, arm)

# The judged arg's field, which its build accepts and missing found not
# required, reads well once its verdict passes.
def fin_fields(+fs: List<&2, Cli.Field>, want: Cli.Want, -u: String,
    -s: String, -l: String, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +id: String, ow: FR(Laws.field_ref(fs, id), kind, attrs),
    arm: {Cli.arg_required_missing(Cli.ArgInfo{id, u, s, l, kind, attrs}, fs)
      == False{} : Bool}) ->
    {Laws.read_at(Cli.want_verdict(want, id, kind, attrs), want,
      Cli.field_values(Cli.field_find(fs, id))) == True{} : Bool}:
  %Equal.sym(Cli.Field, Cli.field_find(fs, id), Laws.field_ref(fs, id),
    Laws.p18_field(fs, id)) :
    {Laws.read_at(Cli.want_verdict(want, id, kind, attrs), want,
      Cli.field_values(_)) == True{} : Bool}
  ff(Laws.field_ref(fs, id), want, kind, attrs, id, ow,
    (%fs_ref(fs, id) : {Bool.or(Bool.and(Cli.has_required(attrs),
      Bool.not(Cli.source_given(_))), Bool.and(Cli.kind_required_pos(kind),
      Bool.not(Cli.source_present(_)))) == False{} : Bool}
    arm))

# What a parse whose build is b reads at verdict v once nothing is missing.
def GBH(b: Cli.FieldBuild, scope: Cli.Scope, v: Maybe<&2, String>,
    id: String, want: Cli.Want) -> Type:
  match b:
    case Cli.Built{+fs}:
      {Cli.scope_missing(scope, fs) == Nil{} : List<&2, String>} ->
      {Laws.read_at(v, want, Cli.field_values(Cli.field_find(fs, id)))
        == True{} : Bool}
    case Cli.BuildFault{fault}: Unit

def gbh_none(b: Cli.FieldBuild, -scope: Cli.Scope, -id: String,
    -name: String, -p: List<&2, String>, -want: Cli.Want) ->
    GBH(b, scope, Cli.arg_verdict(None{}, id, name, p, want), id, want):
  match b:
    case Cli.Built{fs}: em => {==}
    case Cli.BuildFault{fault}: Unit{}

def gbh_of(b: Cli.FieldBuild, -scope: Cli.Scope, +id: String,
    want: Cli.Want, -u: String, -s: String, -l: String,
    +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    ow: OW(b, id, kind, attrs),
    mi: @fs: List<&2, Cli.Field> ->
      {Cli.scope_missing(scope, fs) == Nil{} : List<&2, String>} ->
      {Cli.arg_required_missing(Cli.ArgInfo{id, u, s, l, kind, attrs}, fs)
        == False{} : Bool}) ->
    GBH(b, scope, Cli.want_verdict(want, id, kind, attrs), id, want):
  match b:
    case Cli.Built{+fs}:
      em => fin_fields(fs, want, u, s, l, kind, attrs, id, ow, mi(fs, em))
    case Cli.BuildFault{fault}: Unit{}

def b_dis(hG: Bool, hI: Bool, sS: Bool,
    cov: {Bool.or(Bool.not(hG), sS) == True{} : Bool},
    q: {Bool.or(Bool.not(hI), Bool.not(sS)) == True{} : Bool}) ->
    {Bool.or(Bool.not(hG), Bool.not(hI)) == True{} : Bool}:
  match hG:
    case False{}: {==}
    case True{}:
      match hI:
        case False{}: {==}
        case True{}:
          match sS:
            case True{}:
              Empty.absurd({False{} == True{} : Bool}, false_true_absurd(q))
            case False{}:
              Empty.absurd({False{} == True{} : Bool}, false_true_absurd(cov))

# The scope's own arg r of id builds its field from options or positionals
# as its kind says, and the other side builds no field of id.
def ow_pos(kp: Bool, +G: List<&2, Cli.Item>, +I: List<&2, Cli.Item>,
    +rev: List<&2, Cli.ScanEvent>, +h: Cli.Host, +id: String, +u: String,
    +s: String, +l: String, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +ek: {Cli.kind_pos(kind) == kp : Bool},
    er2: {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
      == Some{Cli.ArgInfo{id, u, s, l, kind, attrs}} : Maybe<&2, Cli.ArgInfo>},
    erI: {Laws.arg_ref(I, id) == Some{Cli.ArgInfo{id, u, s, l, kind, attrs}}
      : Maybe<&2, Cli.ArgInfo>},
    ev: {evs_ok(rev, kind, attrs, id) == True{} : Bool},
    okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    am1GI: {am1(List.append(&2, Cli.Item, G, I), id) == True{} : Bool},
    am1I: {am1(I, id) == True{} : Bool}) ->
    OW(Cli.combine_build(Cli.resolve_options(Cli.spec_items(
      List.append(&2, Cli.Item, G, I)), rev, h), Cli.resolve_positions(
      Cli.spec_slots(Cli.spec_items(I)), Cli.scan_operands(rev), h)), id,
      kind, attrs):
  match kp:
    case True{}:
      nk_ow(Cli.resolve_options(Cli.spec_items(List.append(&2, Cli.Item, G,
        I)), rev, h), Cli.resolve_positions(Cli.spec_slots(Cli.spec_items(I)),
        Cli.scan_operands(rev), h), id, kind, attrs,
        on(List.append(&2, Cli.Item, G, I), rev, h, id,
          Some{Cli.ArgInfo{id, u, s, l, kind, attrs}}, er2, ek, am1GI),
        pi(I, Cli.scan_operands(rev), h, id,
          Cli.ArgInfo{id, u, s, l, kind, attrs}, erI, ek,
          t => a => pos_pg(kind, id, u, s, l, attrs, h, t, a, okd, okl, ek),
          am1I))
    case False{}:
      ow_nk(Cli.resolve_options(Cli.spec_items(List.append(&2, Cli.Item, G,
        I)), rev, h), Cli.resolve_positions(Cli.spec_slots(Cli.spec_items(I)),
        Cli.scan_operands(rev), h), id, kind, attrs,
        oa(List.append(&2, Cli.Item, G, I), rev, h, id,
          Cli.ArgInfo{id, u, s, l, kind, attrs}, er2, ek,
          opt_pg(rev, id, u, s, l, kind, attrs, h, ev, okd, okl, ek), am1GI),
        pn(I, Cli.scan_operands(rev), h, id,
          Some{Cli.ArgInfo{id, u, s, l, kind, attrs}}, erI, ek, am1I))

# An inherited global of id is an option, and the scope's own items then
# hold no arg of id.
def ow_glob(mG: Maybe<&2, Cli.ArgInfo>, +G: List<&2, Cli.Item>,
    +I: List<&2, Cli.Item>, +rev: List<&2, Cli.ScanEvent>, +h: Cli.Host,
    +id: String, +u: String, +s: String, +l: String, +kind: Cli.UsageKind,
    +attrs: List<&2, Cli.Item>,
    +eg: {Laws.arg_ref(G, id) == mG : Maybe<&2, Cli.ArgInfo>},
    +er2: {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
      == Some{Cli.ArgInfo{id, u, s, l, kind, attrs}} : Maybe<&2, Cli.ArgInfo>},
    ev: {evs_ok(rev, kind, attrs, id) == True{} : Bool},
    okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    d: {Bool.or(Bool.not(has(G, id)), Bool.not(has(I, id))) == True{}
      : Bool},
    np: {nonpos(G) == True{} : Bool},
    am1GI: {am1(List.append(&2, Cli.Item, G, I), id) == True{} : Bool},
    am1I: {am1(I, id) == True{} : Bool}) ->
    OW(Cli.combine_build(Cli.resolve_options(Cli.spec_items(
      List.append(&2, Cli.Item, G, I)), rev, h), Cli.resolve_positions(
      Cli.spec_slots(Cli.spec_items(I)), Cli.scan_operands(rev), h)), id,
      kind, attrs):
  match mG:
    case None{}:
      ow_pos(Cli.kind_pos(kind), G, I, rev, h, id, u, s, l, kind, attrs, {==},
        er2, Equal.trans(Maybe<&2, Cli.ArgInfo>, Laws.arg_ref(I, id),
          Laws.arg_ref(List.append(&2, Cli.Item, G, I), id),
          Some{Cli.ArgInfo{id, u, s, l, kind, attrs}},
          Equal.sym(Maybe<&2, Cli.ArgInfo>,
            Laws.arg_ref(List.append(&2, Cli.Item, G, I), id),
            Laws.arg_ref(I, id),
            (%eg : {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
              == Maybe.or(&2, Cli.ArgInfo, _, Laws.arg_ref(I, id))
              : Maybe<&2, Cli.ArgInfo>}
            ref_app(G, I, id))), er2),
        ev, okd, okl, am1GI, am1I)
    case Some{+x}:
      +erx = some_inj(x, Cli.ArgInfo{id, u, s, l, kind, attrs},
        Equal.trans(Maybe<&2, Cli.ArgInfo>, Some{x},
          Laws.arg_ref(List.append(&2, Cli.Item, G, I), id),
          Some{Cli.ArgInfo{id, u, s, l, kind, attrs}},
          Equal.sym(Maybe<&2, Cli.ArgInfo>,
            Laws.arg_ref(List.append(&2, Cli.Item, G, I), id), Some{x},
            (%eg : {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
              == Maybe.or(&2, Cli.ArgInfo, _, Laws.arg_ref(I, id))
              : Maybe<&2, Cli.ArgInfo>}
            ref_app(G, I, id))), er2))
      +enp: {Cli.kind_pos(kind) == False{} : Bool} = (%erx : {Cli.kind_pos(Cli.info_kind(_)) == False{} : Bool}
        ref_np(G, id, x, eg, np))
      ow_nk(Cli.resolve_options(Cli.spec_items(List.append(&2, Cli.Item, G,
        I)), rev, h), Cli.resolve_positions(Cli.spec_slots(Cli.spec_items(I)),
        Cli.scan_operands(rev), h), id, kind, attrs,
        oa(List.append(&2, Cli.Item, G, I), rev, h, id,
          Cli.ArgInfo{id, u, s, l, kind, attrs}, er2, enp,
          opt_pg(rev, id, u, s, l, kind, attrs, h, ev, okd, okl, enp), am1GI),
        pn(I, Cli.scan_operands(rev), h, id, None{}, ref_none(I, id,
          b_nand(has(G, id), has(I, id), d, ref_found(G, id, x, eg))), Unit{},
          am1I))

def ow_scope(+G: List<&2, Cli.Item>, +I: List<&2, Cli.Item>,
    +rev: List<&2, Cli.ScanEvent>, +h: Cli.Host, +id: String, +u: String,
    +s: String, +l: String, +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    er2: {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
      == Some{Cli.ArgInfo{id, u, s, l, kind, attrs}} : Maybe<&2, Cli.ArgInfo>},
    ev: {evs_ok(rev, kind, attrs, id) == True{} : Bool},
    okd: DefaultOk(Cli.find_default(attrs), kind, attrs),
    okl: DelimOk(Cli.find_delim(attrs), kind),
    d: {Bool.or(Bool.not(has(G, id)), Bool.not(has(I, id))) == True{}
      : Bool},
    np: {nonpos(G) == True{} : Bool},
    am1GI: {am1(List.append(&2, Cli.Item, G, I), id) == True{} : Bool},
    am1I: {am1(I, id) == True{} : Bool}) ->
    OW(Cli.combine_build(Cli.resolve_options(List.append(&2, Cli.SpecItem,
      Cli.spec_items(G), Cli.spec_items(I)), rev, h), Cli.resolve_positions(
      Cli.spec_slots(Cli.spec_items(I)), Cli.scan_operands(rev), h)), id,
      kind, attrs):
  %Equal.sym(List<&2, Cli.SpecItem>, List.append(&2, Cli.SpecItem,
    Cli.spec_items(G), Cli.spec_items(I)),
    Cli.spec_items(List.append(&2, Cli.Item, G, I)), spec_append(G, I)) :
    OW(Cli.combine_build(Cli.resolve_options(_, rev, h), Cli.resolve_positions(
      Cli.spec_slots(Cli.spec_items(I)), Cli.scan_operands(rev), h)), id,
      kind, attrs)
  ow_glob(Laws.arg_ref(G, id), G, I, rev, h, id, u, s, l, kind, attrs, {==},
    er2, ev, okd, okl, d, np, am1GI, am1I)

# The arg of id that the scope finds reads well once nothing is missing.
def core_r(k: String, +u: String, +s: String, +l: String,
    +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>, +p: List<&2, String>,
    +I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    +events: List<&2, Cli.ScanEvent>, +h: Cli.Host, +id: String,
    want: Cli.Want,
    +er: {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
      == Some{Cli.ArgInfo{k, u, s, l, kind, attrs}} : Maybe<&2, Cli.ArgInfo>},
    fc: InfoClean(Cli.ArgInfo{k, u, s, l, kind, attrs}),
    +b: {B0(I, G, S, id) == True{} : Bool},
    eG: {ev_all(events, G, id) == True{} : Bool},
    eI: {ev_all(events, I, id) == True{} : Bool}) ->
    GBH(Cli.resolve_scope(Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))},
      List.reverse(&2, Cli.ScanEvent, events), h),
      Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))},
      Cli.want_verdict(want, id, kind, attrs), id, want):
  (okd, rest) = fc
  (okl, okc) = rest
  +er2: {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
      == Some{Cli.ArgInfo{id, u, s, l, kind, attrs}} : Maybe<&2, Cli.ArgInfo>}
    = (%eq_reflect(k, id, ref_key(List.append(&2, Cli.Item, G, I), id,
      Cli.ArgInfo{k, u, s, l, kind, attrs}, er)) :
      {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
        == Some{Cli.ArgInfo{_, u, s, l, kind, attrs}} : Maybe<&2, Cli.ArgInfo>}
    er)
  +qam = b0_qam(I, G, S, id, b)
  +am1I = and_left(am1(I, id), Bool.or(Bool.not(has(I, id)),
    Bool.not(sh(S, id))), qam)
  +d = b_dis(has(G, id), has(I, id), sh(S, id), b0_cov(I, G, S, id, b),
    and_right(am1(I, id), Bool.or(Bool.not(has(I, id)), Bool.not(sh(S, id))),
      qam))
  gbh_of(Cli.resolve_scope(Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))},
    List.reverse(&2, Cli.ScanEvent, events), h),
    Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))}, id, want, u, s, l,
    kind, attrs,
    ow_scope(G, I, List.reverse(&2, Cli.ScanEvent, events), h, id, u, s, l,
      kind, attrs, er2,
      ev_ref(List.reverse(&2, Cli.ScanEvent, events),
        List.append(&2, Cli.Item, G, I), id,
        Cli.ArgInfo{id, u, s, l, kind, attrs},
        ev_rev(events, List.append(&2, Cli.Item, G, I), id,
          ev_app(events, G, I, id, eG, eI)), er2),
      okd, okl, d, b0_np(I, G, S, id, b),
      am1_app(G, I, id, b0_am(I, G, S, id, b), am1I, d), am1I),
    fs => em => mi_go(List.append(&2, Cli.Item, G, I),
      List.append(&2, Cli.SpecItem, Cli.spec_items(G), Cli.spec_items(I)), fs,
      [], id, Cli.ArgInfo{id, u, s, l, kind, attrs}, er2,
      (%spec_append(G, I) : {Cli.missing_items(_, List.append(&2,
        Cli.SpecItem, Cli.spec_items(G), Cli.spec_items(I)), fs, [])
        == Nil{} : List<&2, String>}
      em)))

def core_m(m: Maybe<&2, Cli.ArgInfo>, +p: List<&2, String>,
    +I: List<&2, Cli.Item>, +G: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    +events: List<&2, Cli.ScanEvent>, +h: Cli.Host, +id: String,
    -name: String, want: Cli.Want,
    er: {Laws.arg_ref(List.append(&2, Cli.Item, G, I), id) == m
      : Maybe<&2, Cli.ArgInfo>},
    fc: FoundClean(m), b: {B0(I, G, S, id) == True{} : Bool},
    eG: {ev_all(events, G, id) == True{} : Bool},
    eI: {ev_all(events, I, id) == True{} : Bool}) ->
    GBH(Cli.resolve_scope(Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))},
      List.reverse(&2, Cli.ScanEvent, events), h),
      Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))},
      Cli.arg_verdict(m, id, name, p, want), id, want):
  match m:
    case None{}:
      gbh_none(Cli.resolve_scope(Cli.Scope{p, Cli.spec_node(I,
        Cli.spec_items(G))}, List.reverse(&2, Cli.ScanEvent, events), h),
        Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))}, id, name, p, want)
    case Some{Cli.ArgInfo{k, +u, +s, +l, +kind, +attrs}}:
      core_r(k, u, s, l, kind, attrs, p, I, G, S, events, h, id, want, er, fc,
        b, eG, eI)

# ---- P21 parse chain: each stage either rejects, which matches nothing, or
# hands the next one the build's fact.

def sum_rej(empty: Bool, -c: Cli.Cmd, -path: List<&2, String>,
    -fault: Cli.ScanFault, -id: String, -want: Cli.Want) ->
    Laws.read_parsed(Cli.matches(c, Bool.pick(Cli.ParseResult, empty,
      Cli.SummaryRequired{}, Cli.Rejected{path, fault})), id, want):
  match empty:
    case True{}: Unit{}
    case False{}: Unit{}

def pr(fault: Maybe<&2, Cli.ScanFault>, -path: List<&2, String>,
    -fields: List<&2, Cli.Field>, -external: Maybe<&2, Cli.ExternalArgs>,
    -c: Cli.Cmd, -id: String, -want: Cli.Want,
    fact: {Laws.read_at(Cli.verdict(c, path, id, want), want,
      Cli.field_values(Cli.field_find(fields, id))) == True{} : Bool}) ->
    Laws.read_parsed(Cli.matches(c, Cli.parse_requires(fault, path, fields,
      external)), id, want):
  match fault:
    case Some{problem}: Unit{}
    case None{}: fact

def pc(fault: Maybe<&2, Cli.ScanFault>, +scope: Cli.Scope,
    +fields: List<&2, Cli.Field>, events: List<&2, Cli.ScanEvent>,
    external: Maybe<&2, Cli.ExternalArgs>, -c: Cli.Cmd, -id: String,
    -want: Cli.Want,
    fact: {Laws.read_at(Cli.verdict(c, Cli.scope_path(scope), id, want), want,
      Cli.field_values(Cli.field_find(fields, id))) == True{} : Bool}) ->
    Laws.read_parsed(Cli.matches(c, Cli.parse_conflicts(fault, scope, fields,
      events, external)), id, want):
  match fault:
    case Some{problem}: Unit{}
    case None{}:
      pr(Cli.require_go(Cli.present_order(events, fields),
        Cli.scope_arg_items(scope), fields, None{}), Cli.scope_path(scope),
        fields, external, c, id, want, fact)

def pm(missing: List<&2, String>, +scope: Cli.Scope,
    +fields: List<&2, Cli.Field>, +events: List<&2, Cli.ScanEvent>,
    empty: Bool, external: Maybe<&2, Cli.ExternalArgs>, -c: Cli.Cmd,
    -id: String, -want: Cli.Want,
    em: {Cli.scope_missing(scope, fields) == missing : List<&2, String>},
    g: {Cli.scope_missing(scope, fields) == Nil{} : List<&2, String>} ->
      {Laws.read_at(Cli.verdict(c, Cli.scope_path(scope), id, want), want,
        Cli.field_values(Cli.field_find(fields, id))) == True{} : Bool}) ->
    Laws.read_parsed(Cli.matches(c, Cli.parse_missing(missing, scope, fields,
      events, empty, external)), id, want):
  match missing:
    case Nil{}:
      pc(Cli.conflict_go(Cli.present_order(events, fields), Nil{},
        Cli.scope_arg_items(scope),
        Cli.exclusive_groups(Cli.scope_arg_items(scope)), None{}),
        scope, fields, events, external, c, id, want, g(em))
    case head <> tail:
      sum_rej(empty, c, Cli.scope_path(scope), Cli.E06{head <> tail}, id,
        want)

def pb(build: Cli.FieldBuild, +scope: Cli.Scope,
    +events: List<&2, Cli.ScanEvent>, empty: Bool,
    external: Maybe<&2, Cli.ExternalArgs>, -c: Cli.Cmd, -id: String,
    -want: Cli.Want,
    g: GBH(build, scope, Cli.verdict(c, Cli.scope_path(scope), id, want), id,
      want)) ->
    Laws.read_parsed(Cli.matches(c, Cli.parse_built(build, scope, events, empty,
      external)), id, want):
  match build:
    case Cli.BuildFault{fault}: Unit{}
    case Cli.Built{+fields}:
      pm(Cli.scope_missing(scope, fields), scope, fields, events, empty,
        external, c, id, want, {==}, g)

def pni(needs: Bool, +scope: Cli.Scope, +events: List<&2, Cli.ScanEvent>,
    +h: Cli.Host, +empty: Bool, external: Maybe<&2, Cli.ExternalArgs>,
    -c: Cli.Cmd, -id: String, -want: Cli.Want,
    g: GBH(Cli.resolve_scope(scope, events, h), scope,
      Cli.verdict(c, Cli.scope_path(scope), id, want), id, want)) ->
    Laws.read_parsed(Cli.matches(c, Cli.parse_no_issue(needs, scope, events, h,
      empty, external)), id, want):
  match needs:
    case True{}: sum_rej(empty, c, Cli.scope_path(scope), Cli.E10{}, id, want)
    case False{}:
      pb(Cli.resolve_scope(scope, events, h), scope, events, empty, external,
        c, id, want, g)

def pis(issue: Maybe<&2, Cli.ScanFault>, +scope: Cli.Scope,
    events: List<&2, Cli.ScanEvent>, h: Cli.Host, empty: Bool,
    external: Maybe<&2, Cli.ExternalArgs>, -c: Cli.Cmd, -id: String,
    -want: Cli.Want,
    g: GBH(Cli.resolve_scope(scope, events, h), scope,
      Cli.verdict(c, Cli.scope_path(scope), id, want), id, want)) ->
    Laws.read_parsed(Cli.matches(c, Cli.parse_issue(issue, scope, events, h, empty,
      external)), id, want):
  match issue:
    case Some{fault}: Unit{}
    case None{}:
      pni(Cli.scope_needs_sub(scope), scope, events, h, empty, external, c,
        id, want, g)

def pe(found: Maybe<&2, Cli.Early>, +scope: Cli.Scope,
    events: List<&2, Cli.ScanEvent>, h: Cli.Host, empty: Bool,
    issue: Maybe<&2, Cli.ScanFault>, external: Maybe<&2, Cli.ExternalArgs>,
    -c: Cli.Cmd, -id: String, -want: Cli.Want,
    g: GBH(Cli.resolve_scope(scope, events, h), scope,
      Cli.verdict(c, Cli.scope_path(scope), id, want), id, want)) ->
    Laws.read_parsed(Cli.matches(c, Cli.parse_early(found, scope, events, h, empty,
      issue, external)), id, want):
  match found:
    case Some{Cli.EarlyHelp{long}}: Unit{}
    case Some{Cli.EarlyVersion{}}: Unit{}
    case None{}: pis(issue, scope, events, h, empty, external, c, id, want, g)

# The build fact for the scope a scan ends in, which its invariant names.
def pfs_g(-scope: Cli.Scope, +events: List<&2, Cli.ScanEvent>, +h: Cli.Host,
    +name: String, -about: String, +items0: List<&2, Cli.Item>, +id: String,
    +want: Cli.Want, +p: List<&2, String>, +I: List<&2, Cli.Item>,
    +G: List<&2, Cli.Item>, +S: List<&2, Cli.Seen>,
    es: {scope == Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))}
      : Cli.Scope},
    ei: {hi(p, items0) == I : List<&2, Cli.Item>},
    eg: {hg(p, items0, Nil{}) == G : List<&2, Cli.Item>},
    b: {B0(I, G, S, id) == True{} : Bool},
    eG: {ev_all(events, G, id) == True{} : Bool},
    eI: {ev_all(events, I, id) == True{} : Bool}, dc: DeepClean(items0)) ->
    GBH(Cli.resolve_scope(scope, List.reverse(&2, Cli.ScanEvent, events), h),
      scope, Cli.verdict(Cli.Cmd{name, about, items0}, Cli.scope_path(scope),
      id, want), id, want):
  +e1: {Cli.find_arg_info(Cli.scope_args(p, items0, Nil{}), id)
      == Laws.arg_ref(List.append(&2, Cli.Item, G, I), id)
      : Maybe<&2, Cli.ArgInfo>} = (%ei : {Cli.find_arg_info(Cli.scope_args(p, items0, Nil{}), id)
      == Laws.arg_ref(List.append(&2, Cli.Item, G, _), id)
      : Maybe<&2, Cli.ArgInfo>}
    (%eg : {Cli.find_arg_info(Cli.scope_args(p, items0, Nil{}), id)
        == Laws.arg_ref(List.append(&2, Cli.Item, _, hi(p, items0)), id)
        : Maybe<&2, Cli.ArgInfo>}
      (%sa_hg(p, items0, Nil{}) :
          {Cli.find_arg_info(Cli.scope_args(p, items0, Nil{}), id)
          == Laws.arg_ref(_, id) : Maybe<&2, Cli.ArgInfo>}
        Laws.p18_arg(Cli.scope_args(p, items0, Nil{}), id))))
  %Equal.sym(Cli.Scope, scope, Cli.Scope{p, Cli.spec_node(I,
    Cli.spec_items(G))}, es) :
    GBH(Cli.resolve_scope(_, List.reverse(&2, Cli.ScanEvent, events), h), _,
      Cli.verdict(Cli.Cmd{name, about, items0}, Cli.scope_path(_), id, want),
      id, want)
  %Equal.sym(Maybe<&2, Cli.ArgInfo>,
    Cli.find_arg_info(Cli.scope_args(p, items0, Nil{}), id),
    Laws.arg_ref(List.append(&2, Cli.Item, G, I), id), e1) :
    GBH(Cli.resolve_scope(Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))},
      List.reverse(&2, Cli.ScanEvent, events), h),
      Cli.Scope{p, Cli.spec_node(I, Cli.spec_items(G))},
      Cli.arg_verdict(_, id, name, p, want), id, want)
  core_m(Laws.arg_ref(List.append(&2, Cli.Item, G, I), id), p, I, G, S,
    events, h, id, name, want, {==},
    (%e1 : FoundClean(_)
    find_clean(Cli.scope_args(p, items0, Nil{}), None{}, id,
      deep_scope(p, items0, Nil{}, dc, Unit{}), Unit{})),
    b, eG, eI)

def pfs(state: Cli.ScanState, +h: Cli.Host, empty: Bool, +name: String,
    -about: String, +items0: List<&2, Cli.Item>, +id: String,
    +want: Cli.Want, inv: SInv(state, items0, id), dc: DeepClean(items0)) ->
    Laws.read_parsed(Cli.matches(Cli.Cmd{name, about, items0},
      Cli.parse_from_state(state, h, empty)), id, want):
  match state:
    case Cli.ScanState{+scope, +events, resting, count, external, issue}:
      match inv:
        case (+p, (+I, (+G, (+S, (es, (ei, (eg, (b, (eG, eI))))))))):
          pe(Cli.find_early(List.reverse(&2, Cli.ScanEvent, events)), scope,
            List.reverse(&2, Cli.ScanEvent, events), h, empty, issue,
            external, Cli.Cmd{name, about, items0}, id, want,
            pfs_g(scope, events, h, name, about, items0, id, want, p, I, G, S,
              es, ei, eg, b, eG, eI, dc))

# ---- P21: the law.

def q_take(+name: String, -about: String, +items: List<&2, Cli.Item>,
    parts: AllNil(top_list(name, about, items))) ->
    {qt(items, Nil{}, Cli.global_entries(Cli.lint_items(items))) == True{}
      : Bool}:
  (p1, r1) = parts
  (p2, r2) = r1
  (p3, r3) = r2
  qtree(items, name, Cli.scope_ids(Cli.lint_items(items)), Nil{},
    Cli.global_entries(Cli.lint_items(items)), False{}, False{},
    Cli.has_version_item(items), True{}, p3)

def lint_qt(+name: String, +about: String, +items: List<&2, Cli.Item>,
    e: {Cli.problems(Cli.Cmd{name, about, items}) == Nil{}
      : List<&2, Cli.Problem>}) ->
    {qt(items, Nil{}, Cli.global_entries(Cli.lint_items(items))) == True{}
      : Bool}:
  q_take(name, about, items, concat_all(top_list(name, about, items), e))

def p21_go(c: Cli.Cmd, h: Cli.Host, +argv: List<&2, String>, +id: String,
    +want: Cli.Want, +e: {Cli.problems(c) == [] : List<&2, Cli.Problem>}) ->
    Laws.read_parsed(Cli.matches(c, Cli.parse(c, h, argv)), id, want):
  match c:
    case Cli.Cmd{+name, +about, +items}:
      pfs(Cli.scan_close(Cli.scan_go(argv, Cli.Open{Cli.scan_start(
        Cli.Cmd{name, about, items})})), h, List.is_empty(&2, String, argv),
        name, about, items, id, want,
        scan_inv(items, name, about, argv, id, lint_qt(name, about, items, e)),
        lint_clean(name, about, items, e))

def Laws.p21(c, h, argv, id, want, e):
  p21_go(c, h, argv, id, want, e)

# P22 nat: Nat.read.go reads a string exactly when decimal_digits holds,
# since both apply the same test to each char, and Nat.read.trim keeps
# decimal_digits' answer.

def nat_go_if(ok: Bool, t: String, acc: Nat, d: U32,
    ih: @a: Nat -> {Cli.decimal_digits(t)
      == Maybe.is_some(&2, Nat, Nat.read.go(t, a)) : Bool}) ->
    {Bool.and(ok, Cli.decimal_digits(t))
      == Maybe.is_some(&2, Nat, Nat.read.if(t, acc, d, ok)) : Bool}:
  match ok:
    case True{}: ih(Nat.add(Nat.mul(acc, 10n), U32.to_nat(d)))
    case False{}: {==}

def nat_go(s: String, acc: Nat) ->
    {Cli.decimal_digits(s) == Maybe.is_some(&2, Nat, Nat.read.go(s, acc))
      : Bool}:
  match s:
    case SNil{}: {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          nat_go_if(U32.is_lt(U32.sub(x, 48), 10), t, acc, U32.sub(x, 48),
            a => nat_go(t, a))

# Nat.read.trim on a string that does not start with '0'.
def TrimOther(c: Char) -> Type:
  @t: String -> {SCon{c, t} == Nat.read.trim(SCon{c, t}) : String}

def TrimView(c: Char) -> Type:
  {Chr{48} == c : Char} | TrimOther(c)

# Arms: python3 tools/charsplit.py 't => {==}' 48
def trim_view(c: Char) -> TrimView(c):
  match c:
    case Chr{U32{WCon{True{}, _}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{True{}, _}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inl{{==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}}}:
      Inr{t => {==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}}}:
      Inr{t => {==}}

def trim_at(-c: Char, t: String, v: TrimView(c),
    ih: {Cli.decimal_digits(Nat.read.trim(t)) == Cli.decimal_digits(t)
      : Bool}) ->
    {Cli.decimal_digits(Nat.read.trim(SCon{c, t}))
      == Cli.decimal_digits(SCon{c, t}) : Bool}:
  match v:
    case Inl{e}:
      %e : {Cli.decimal_digits(Nat.read.trim(SCon{_, t}))
        == Cli.decimal_digits(SCon{_, t}) : Bool}
      ih
    case Inr{o}:
      %o(t) : {Cli.decimal_digits(_) == Cli.decimal_digits(SCon{c, t}) : Bool}
      {==}

# Trimming leading zeroes keeps decimal_digits' answer.
def nat_trim(s: String) ->
    {Cli.decimal_digits(Nat.read.trim(s)) == Cli.decimal_digits(s) : Bool}:
  match s:
    case SNil{}: {==}
    case SCon{+c, +t}: trim_at(c, t, trim_view(c), nat_trim(t))

def and_true_r(b: Bool) -> {b == Bool.and(b, True{}) : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def and_false_r(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def nat_gate(f: Bool, +s: String) ->
    {Bool.and(Cli.decimal_digits(s), f)
      == Maybe.is_some(&2, Nat, Nat.read.gate(Nat.read.trim(s), f)) : Bool}:
  match f:
    case True{}:
      %and_true_r(Cli.decimal_digits(s)) :
        {_ == Maybe.is_some(&2, Nat, Nat.read.go(Nat.read.trim(s), 0n)) : Bool}
      %nat_trim(s) :
        {_ == Maybe.is_some(&2, Nat, Nat.read.go(Nat.read.trim(s), 0n)) : Bool}
      nat_go(Nat.read.trim(s), 0n)
    case False{}: and_false_r(Cli.decimal_digits(s))

def p22_nat_go(+v: String) ->
    {Cli.valid_nat(v) == Maybe.is_some(&2, Nat, Nat.read(v)) : Bool}:
  match v:
    case SNil{}: {==}
    case SCon{+h, +t}:
      nat_gate(Nat.read.fits(Nat.read.trim(SCon{h, t})), SCon{h, t})

def Laws.p22_nat(v):
  p22_nat_go(v)

# valid_u32 is U32.read's answer.
def Laws.p22_u32(v):
  {==}

# P22 choose: a passing choose verdict leaves choose_fits and keys_verdict's
# test true, and all_in is read_keys.

def or_left(a: Maybe<&2, String>, -b: Maybe<&2, String>,
    e: {Maybe.or(&2, String, a, b) == None{} : Maybe<&2, String>}) ->
    {a == None{} : Maybe<&2, String>}:
  match a:
    case None{}: {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, String>},
        why_some_absurd(x, e))

def or_right(a: Maybe<&2, String>, -b: Maybe<&2, String>,
    e: {Maybe.or(&2, String, a, b) == None{} : Maybe<&2, String>}) ->
    {b == None{} : Maybe<&2, String>}:
  match a:
    case None{}: e
    case Some{x}:
      Empty.absurd({b == None{} : Maybe<&2, String>}, why_some_absurd(x, e))

def kind_false_absurd(-id: String, -kind: Cli.UsageKind,
    -attrs: List<&2, Cli.Item>,
    e: {Cli.kind_verdict(False{}, id, kind, attrs) == None{}
      : Maybe<&2, String>}) -> Empty:
  %e : why_none_disc(_)
  Unit{}

def kind_none(fits: Bool, -id: String, -kind: Cli.UsageKind,
    -attrs: List<&2, Cli.Item>,
    e: {Cli.kind_verdict(fits, id, kind, attrs) == None{}
      : Maybe<&2, String>}) -> {fits == True{} : Bool}:
  match fits:
    case True{}: {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool},
        kind_false_absurd(id, kind, attrs, e))

def fits_some(+kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    e: {Cli.choose_fits(kind, attrs) == True{} : Bool}) ->
    {Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs)) == True{}
      : Bool}:
  and_right(Bool.not(Cli.kind_many(kind)),
    Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs)),
    and_right(Cli.kind_valued(kind), Bool.and(Bool.not(Cli.kind_many(kind)),
      Maybe.is_some(&2, List<&2, String>, Cli.find_one_of(attrs))), e))

def all_in_ref(xs: List<&2, String>, +ys: List<&2, String>) ->
    {Cli.all_in(xs, ys) == Laws.read_keys(xs, ys) : Bool}:
  match xs:
    case Nil{}: {==}
    case head <> tail:
      %all_in_ref(tail, ys) :
        {Bool.and(List.contains(~String, ~String.eq, ys, head),
          Cli.all_in(tail, ys))
          == Bool.and(List.contains(~String, ~String.eq, ys, head), _)
          : Bool}
      {==}

def keys_are_ok(found: Maybe<&2, List<&2, String>>, +keys: List<&2, String>,
    -id: String,
    es: {Maybe.is_some(&2, List<&2, String>, found) == True{} : Bool},
    e: {Cli.keys_verdict(found, keys, id) == None{} : Maybe<&2, String>}) ->
    {Laws.keys_are(keys, found) == True{} : Bool}:
  match found:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, false_true_absurd(es))
    case Some{+values}:
      %all_in_ref(keys, values) :
        {Bool.and(Bool.not(List.is_empty(&2, String, keys)),
          Bool.and(_, Laws.read_keys(values, keys))) == True{} : Bool}
      %all_in_ref(values, keys) :
        {Bool.and(Bool.not(List.is_empty(&2, String, keys)),
          Bool.and(Cli.all_in(keys, values), _)) == True{} : Bool}
      keys_none(Bool.and(Bool.not(List.is_empty(&2, String, keys)),
        Bool.and(Cli.all_in(keys, values), Cli.all_in(values, keys))), id, e)

def p22_choose_go(opt: Bool, +keys: List<&2, String>, +id: String,
    +kind: Cli.UsageKind, +attrs: List<&2, Cli.Item>,
    +e: {Cli.want_verdict(Cli.WChoose{opt, keys}, id, kind, attrs)
      == None{} : Maybe<&2, String>}) ->
    {Laws.keys_are(keys, Cli.find_one_of(attrs)) == True{} : Bool}:
  keys_are_ok(Cli.find_one_of(attrs), keys, id,
    fits_some(kind, attrs, kind_none(Cli.choose_fits(kind, attrs), id, kind,
      attrs, or_left(Cli.kind_verdict(Cli.choose_fits(kind, attrs), id, kind,
        attrs), Maybe.or(&2, String, Cli.absent_verdict(Bool.and(
          Bool.not(opt), Cli.may_absent(kind, attrs)), id, "choose"),
          Cli.keys_verdict(Cli.find_one_of(attrs), keys, id)), e))),
    or_right(Cli.absent_verdict(Bool.and(Bool.not(opt),
      Cli.may_absent(kind, attrs)), id, "choose"),
      Cli.keys_verdict(Cli.find_one_of(attrs), keys, id),
      or_right(Cli.kind_verdict(Cli.choose_fits(kind, attrs), id, kind,
        attrs), Maybe.or(&2, String, Cli.absent_verdict(Bool.and(
          Bool.not(opt), Cli.may_absent(kind, attrs)), id, "choose"),
          Cli.keys_verdict(Cli.find_one_of(attrs), keys, id)), e)))

def Laws.p22_choose(opt, keys, id, kind, attrs, e):
  p22_choose_go(opt, keys, id, kind, attrs, e)

def Laws.g_check_sample_values():
  {==}

def Laws.g_check_pkg():
  {==}

def Laws.g_lint_decode_bug():
  {==}

def Laws.g_read_values():
  ({==}, {==})

def Laws.g_read_absent():
  ({==}, {==})

def Laws.g_read_route():
  ({==}, ({==}, {==}))

def Laws.g_read_first_match():
  ({==}, {==})

def Laws.g_read_route_faults():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_read_external():
  ({==}, {==})

def Laws.g_read_pkg():
  ({==}, ({==}, ({==}, {==})))

# P7 and P8: the --color pre-scan and the environment rules.

def stop_keep(argv: List<&2, String>, +y: Maybe<&2, String>) ->
    {Cli.ColorStop{y} == Cli.color_scan(argv, Cli.ColorStop{y})
      : Cli.Prescan}:
  match argv:
    case Nil{}: {==}
    case token <> tail: stop_keep(tail, y)

def seek_step(d: Bool, b: Bool, a: Bool, n: Bool, token: String,
    +tail: List<&2, String>, +y: Maybe<&2, String>,
    quiet: {Bool.and(Bool.not(d), Bool.or(Bool.or(b, a), n)) == False{}
      : Bool},
    ih: @q: {n == False{} : Bool} -> {Cli.color_value(y) ==
      Cli.color_pick(Cli.color_scan(tail, Cli.ColorSeek{y}))
      : Maybe<&2, Bool>}) ->
    {Cli.color_value(y) == Cli.color_pick(Cli.color_scan(tail,
      Cli.color_seek(d, b, a, token, y))) : Maybe<&2, Bool>}:
  match d b a:
    case True{} _ _:
      %stop_keep(tail, y) :
        {Cli.color_value(y) == Cli.color_pick(_) : Maybe<&2, Bool>}
      {==}
    case False{} True{} _:
      Empty.absurd({Cli.color_value(y) == Cli.color_pick(Cli.color_scan(tail,
        Cli.ColorWant{})) : Maybe<&2, Bool>}, true_false_absurd(quiet))
    case False{} False{} True{}:
      Empty.absurd({Cli.color_value(y) == Cli.color_pick(Cli.color_scan(tail,
        Cli.ColorSeek{Some{String.drop(token, 8n)}})) : Maybe<&2, Bool>},
        true_false_absurd(quiet))
    case False{} False{} False{}: ih(quiet)

# A scan from a seeking state over argv that never names --color before a
# `--` ends with the value it started with.
def seek_keep(argv: List<&2, String>, +y: Maybe<&2, String>,
    quiet: {Laws.names_color(argv) == False{} : Bool}) ->
    {Cli.color_value(y) == Cli.color_pick(Cli.color_scan(argv,
      Cli.ColorSeek{y})) : Maybe<&2, Bool>}:
  match argv:
    case Nil{}: {==}
    case +token <> +tail:
      seek_step(String.eq(token, "--"), String.eq(token, "--color"),
        String.starts_with(token, "--color="), Laws.names_color(tail), token,
        tail, y, quiet, q => seek_keep(tail, y, q))

def flag_quiet(enabled: Bool, argv: List<&2, String>,
    quiet: {Laws.names_color(argv) == False{} : Bool}) ->
    {None{} == Cli.color_flag(enabled, argv) : Maybe<&2, Bool>}:
  match enabled:
    case True{}: seek_keep(argv, None{}, quiet)
    case False{}: {==}

def p7_rules(s: Bool, vars: List<&2, Cli.Var>, out_tty: Bool,
    err_tty: Bool, width: Nat, e: {s == True{} : Bool}) ->
    {Laws.colors(Cli.term_env(Cli.env_rules(s, vars), out_tty, err_tty,
      width)) == (False{}, False{}) : (Bool & Bool)}:
  match s:
    case True{}: {==}
    case False{}:
      Empty.absurd({Laws.colors(Cli.term_env(Cli.env_rules(False{}, vars),
        out_tty, err_tty, width)) == (False{}, False{}) : (Bool & Bool)},
        false_true_absurd(e))

def p7_found(found: Maybe<&2, String>, vars: List<&2, Cli.Var>,
    out_tty: Bool, err_tty: Bool, width: Nat,
    e: {Laws.set_nonempty(found) == True{} : Bool}) ->
    {Laws.colors(Cli.term_env(Cli.env_rules(Cli.var_set(found), vars),
      out_tty, err_tty, width)) == (False{}, False{}) : (Bool & Bool)}:
  match found:
    case None{}:
      Empty.absurd({Laws.colors(Cli.term_env(Cli.env_rules(False{}, vars),
        out_tty, err_tty, width)) == (False{}, False{}) : (Bool & Bool)},
        false_true_absurd(e))
    case Some{value}:
      p7_rules(Bool.not(String.is_empty(value)), vars, out_tty, err_tty,
        width, e)

def Laws.p7(c, h, argv, no_color, quiet):
  match c h:
    case Cli.Cmd{name, about, items} Cli.Host{width, +vars, out_tty, err_tty}:
      %flag_quiet(Cli.has_color(items), argv, quiet) :
        {Laws.colors(Cli.term_for(_, vars, out_tty, err_tty, width))
          == (False{}, False{}) : (Bool & Bool)}
      p7_found(Cli.var_value(vars, "NO_COLOR"), vars, out_tty, err_tty, width,
        no_color)

def has_color_mid(before: List<&2, Cli.Item>, after: List<&2, Cli.Item>) ->
    {True{} == Cli.has_color(List.append(&2, Cli.Item, before,
      Cli.color() <> after)) : Bool}:
  match before:
    case Nil{}: {==}
    case +item <> tail:
      %has_color_mid(tail, after) :
        {True{} == Bool.or(Cli.is_color(item), _) : Bool}
      Equal.sym(Bool, Bool.or(Cli.is_color(item), True{}), True{},
        or_true_right(Cli.is_color(item)))

def flag_on(enabled: Bool, argv: List<&2, String>,
    e: {True{} == enabled : Bool}) ->
    {Cli.color_pick(Cli.color_scan(argv, Cli.ColorSeek{None{}})) ==
      Cli.color_flag(enabled, argv) : Maybe<&2, Bool>}:
  %e : {Cli.color_pick(Cli.color_scan(argv, Cli.ColorSeek{None{}})) ==
    Cli.color_flag(_, argv) : Maybe<&2, Bool>}
  {==}

# Seeking or waiting for a --color value: not past a `--`.
def scan_open(s: Cli.Prescan) -> Data:
  match s:
    case Cli.ColorSeek{last}: Unit
    case Cli.ColorWant{}: Unit
    case Cli.ColorStop{last}: Empty

def seek_open(d: Bool, b: Bool, a: Bool, token: String,
    y: Maybe<&2, String>, e: {d == False{} : Bool}) ->
    scan_open(Cli.color_seek(d, b, a, token, y)):
  match d b a:
    case True{} _ _: true_false_absurd(e)
    case False{} True{} _: Unit{}
    case False{} False{} True{}: Unit{}
    case False{} False{} False{}: Unit{}

def want_open(f: Bool, +token: String,
    e: {String.eq(token, "--") == False{} : Bool}) ->
    scan_open(Cli.color_want(f, token)):
  match f:
    case False{}: Unit{}
    case True{}:
      seek_open(String.eq(token, "--"), String.eq(token, "--color"),
        String.starts_with(token, "--color="), token, Some{""}, e)

def step_open(s: Cli.Prescan, +token: String, open: scan_open(s),
    e: {String.eq(token, "--") == False{} : Bool}) ->
    scan_open(Cli.color_step(s, token)):
  match s:
    case Cli.ColorSeek{last}:
      seek_open(String.eq(token, "--"), String.eq(token, "--color"),
        String.starts_with(token, "--color="), token, last, e)
    case Cli.ColorWant{}: want_open(String.starts_with(token, "-"), token, e)
    case Cli.ColorStop{last}: open

def any_false_head(b: Bool, -c: Bool,
    e: {List.any.if(u => c, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false_absurd(e))
    case False{}: {==}

def any_false_tail(b: Bool, -c: Bool,
    e: {List.any.if(u => c, b) == False{} : Bool}) -> {c == False{} : Bool}:
  match b:
    case True{}: Empty.absurd({c == False{} : Bool}, true_false_absurd(e))
    case False{}: e

# A prefix with no `--` leaves the pre-scan open for what follows it.
def pre_pick(pre: List<&2, String>, +rest: List<&2, String>,
    +s: Cli.Prescan, +b: Bool, open: scan_open(s),
    +clear: {List.contains(~String, ~String.eq, pre, "--") == False{}
      : Bool},
    hit: @t: Cli.Prescan -> scan_open(t) -> {Some{b} ==
      Cli.color_pick(Cli.color_scan(rest, t)) : Maybe<&2, Bool>}) ->
    {Some{b} == Cli.color_pick(Cli.color_scan(List.append(&2, String, pre,
      rest), s)) : Maybe<&2, Bool>}:
  match pre:
    case Nil{}: hit(s, open)
    case +token <> +tail:
      pre_pick(tail, rest, Cli.color_step(s, token), b,
        step_open(s, token, open, any_false_head(String.eq(token, "--"),
          List.contains(~String, ~String.eq, tail, "--"), clear)),
        any_false_tail(String.eq(token, "--"),
          List.contains(~String, ~String.eq, tail, "--"), clear), hit)

def hit_never(+post: List<&2, String>,
    +quiet: {Laws.names_color(post) == False{} : Bool}, t: Cli.Prescan,
    open: scan_open(t)) ->
    {Some{False{}} == Cli.color_pick(Cli.color_scan(List.append(&2, String,
      ["--color=never"], post), t)) : Maybe<&2, Bool>}:
  match t:
    case Cli.ColorSeek{last}: seek_keep(post, Some{"never"}, quiet)
    case Cli.ColorWant{}: seek_keep(post, Some{"never"}, quiet)
    case Cli.ColorStop{last}:
      Empty.absurd({Some{False{}} == Cli.color_pick(Cli.color_scan(
        "--color=never" <> post, Cli.ColorStop{last})) : Maybe<&2, Bool>},
        open)

def hit_always(+post: List<&2, String>,
    +quiet: {Laws.names_color(post) == False{} : Bool}, t: Cli.Prescan,
    open: scan_open(t)) ->
    {Some{True{}} == Cli.color_pick(Cli.color_scan(List.append(&2, String,
      ["--color=always"], post), t)) : Maybe<&2, Bool>}:
  match t:
    case Cli.ColorSeek{last}: seek_keep(post, Some{"always"}, quiet)
    case Cli.ColorWant{}: seek_keep(post, Some{"always"}, quiet)
    case Cli.ColorStop{last}:
      Empty.absurd({Some{True{}} == Cli.color_pick(Cli.color_scan(
        "--color=always" <> post, Cli.ColorStop{last})) : Maybe<&2, Bool>},
        open)

def hit_never_apart(+post: List<&2, String>,
    +quiet: {Laws.names_color(post) == False{} : Bool}, t: Cli.Prescan,
    open: scan_open(t)) ->
    {Some{False{}} == Cli.color_pick(Cli.color_scan(List.append(&2, String,
      ["--color", "never"], post), t)) : Maybe<&2, Bool>}:
  match t:
    case Cli.ColorSeek{last}: seek_keep(post, Some{"never"}, quiet)
    case Cli.ColorWant{}: seek_keep(post, Some{"never"}, quiet)
    case Cli.ColorStop{last}:
      Empty.absurd({Some{False{}} == Cli.color_pick(Cli.color_scan(
        "--color" <> "never" <> post, Cli.ColorStop{last}))
        : Maybe<&2, Bool>}, open)

def hit_always_apart(+post: List<&2, String>,
    +quiet: {Laws.names_color(post) == False{} : Bool}, t: Cli.Prescan,
    open: scan_open(t)) ->
    {Some{True{}} == Cli.color_pick(Cli.color_scan(List.append(&2, String,
      ["--color", "always"], post), t)) : Maybe<&2, Bool>}:
  match t:
    case Cli.ColorSeek{last}: seek_keep(post, Some{"always"}, quiet)
    case Cli.ColorWant{}: seek_keep(post, Some{"always"}, quiet)
    case Cli.ColorStop{last}:
      Empty.absurd({Some{True{}} == Cli.color_pick(Cli.color_scan(
        "--color" <> "always" <> post, Cli.ColorStop{last}))
        : Maybe<&2, Bool>}, open)

def p8_at(name: String, about: String, before: List<&2, Cli.Item>,
    after: List<&2, Cli.Item>, h: Cli.Host, pre: List<&2, String>,
    post: List<&2, String>, chosen: List<&2, String>) -> (Bool & Bool):
  Laws.colors_around(Cli.cmd(name, about, List.append(&2, Cli.Item, before,
    Cli.color() <> after)), h, pre, post, chosen)

# One spelling: whatever chosen leaves after an open pre-scan decides both
# streams.
def around(name: String, about: String, +before: List<&2, Cli.Item>,
    +after: List<&2, Cli.Item>, h: Cli.Host, +pre: List<&2, String>,
    +post: List<&2, String>, +chosen: List<&2, String>, +b: Bool,
    clear: {List.contains(~String, ~String.eq, pre, "--") == False{} : Bool},
    hit: @t: Cli.Prescan -> scan_open(t) -> {Some{b} ==
      Cli.color_pick(Cli.color_scan(List.append(&2, String, chosen, post), t))
      : Maybe<&2, Bool>}) ->
    {p8_at(name, about, before, after, h, pre, post, chosen) == (b, b)
      : (Bool & Bool)}:
  match h:
    case Cli.Host{width, vars, out_tty, err_tty}:
      %Equal.trans(Maybe<&2, Bool>, Some{b},
        Cli.color_pick(Cli.color_scan(List.append(&2, String, pre,
          List.append(&2, String, chosen, post)), Cli.ColorSeek{None{}})),
        Cli.color_flag(Cli.has_color(List.append(&2, Cli.Item, before,
          Cli.color() <> after)), List.append(&2, String, pre,
          List.append(&2, String, chosen, post))),
        pre_pick(pre, List.append(&2, String, chosen, post),
          Cli.ColorSeek{None{}}, b, Unit{}, clear, hit),
        flag_on(Cli.has_color(List.append(&2, Cli.Item, before,
          Cli.color() <> after)), List.append(&2, String, pre,
          List.append(&2, String, chosen, post)),
          has_color_mid(before, after))) :
        {Laws.colors(Cli.term_for(_, vars, out_tty, err_tty, width)) == (b, b)
          : (Bool & Bool)}
      {==}

def list4_eq(-A: Type, -a1: A, -a2: A, -a3: A, -a4: A, -b1: A, -b2: A,
    -b3: A, -b4: A, e1: {a1 == b1 : A}, e2: {a2 == b2 : A},
    e3: {a3 == b3 : A}, e4: {a4 == b4 : A}) ->
    {[a1, a2, a3, a4] == [b1, b2, b3, b4] : List<A>}:
  %e1 : {[a1, a2, a3, a4] == [_, b2, b3, b4] : List<A>}
  %e2 : {[a1, a2, a3, a4] == [a1, _, b3, b4] : List<A>}
  %e3 : {[a1, a2, a3, a4] == [a1, a2, _, b4] : List<A>}
  %e4 : {[a1, a2, a3, a4] == [a1, a2, a3, _] : List<A>}
  {==}

def p8_list(+name: String, +about: String, +before: List<&2, Cli.Item>,
    +after: List<&2, Cli.Item>, +h: Cli.Host, +pre: List<&2, String>,
    +post: List<&2, String>,
    +clear: {List.contains(~String, ~String.eq, pre, "--") == False{} : Bool},
    +quiet: {Laws.names_color(post) == False{} : Bool}) ->
    {[p8_at(name, about, before, after, h, pre, post, ["--color=never"]),
      p8_at(name, about, before, after, h, pre, post, ["--color=always"]),
      p8_at(name, about, before, after, h, pre, post, ["--color", "never"]),
      p8_at(name, about, before, after, h, pre, post, ["--color", "always"])]
      == [(False{}, False{}), (True{}, True{}), (False{}, False{}),
        (True{}, True{})] : List<(Bool & Bool)>}:
  list4_eq((Bool & Bool),
    p8_at(name, about, before, after, h, pre, post, ["--color=never"]),
    p8_at(name, about, before, after, h, pre, post, ["--color=always"]),
    p8_at(name, about, before, after, h, pre, post, ["--color", "never"]),
    p8_at(name, about, before, after, h, pre, post, ["--color", "always"]),
    (False{}, False{}), (True{}, True{}), (False{}, False{}),
    (True{}, True{}),
    around(name, about, before, after, h, pre, post, ["--color=never"],
      False{}, clear, t => o => hit_never(post, quiet, t, o)),
    around(name, about, before, after, h, pre, post, ["--color=always"],
      True{}, clear, t => o => hit_always(post, quiet, t, o)),
    around(name, about, before, after, h, pre, post, ["--color", "never"],
      False{}, clear, t => o => hit_never_apart(post, quiet, t, o)),
    around(name, about, before, after, h, pre, post, ["--color", "always"],
      True{}, clear, t => o => hit_always_apart(post, quiet, t, o)))

def Laws.p8(name, about, before, after, h, pre, post, clear, quiet):
  p8_list(name, about, before, after, h, pre, post, clear, quiet)

def Laws.g_help_root():
  ({==}, {==})

def Laws.g_help_sub():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_help_width():
  ({==}, {==})

def Laws.g_help_paragraphs():
  ({==}, {==})

def Laws.g_help_sections():
  ({==}, {==})

def Laws.g_help_env_names():
  {==}

def Laws.g_help_usage():
  ({==}, {==})

def Laws.g_help_global_groups():
  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))

def Laws.g_help_outcome():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))

def Laws.g_err_format():
  {==}

def Laws.g_err_scan():
  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))

def Laws.g_err_check():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.g_err_precedence():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_tip_scope():
  ({==}, ({==}, {==}))

def Laws.g_tip_suggest():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_tip_order():
  {==}

def Laws.g_tip_candidates():
  ({==}, ({==}, {==}))

def Laws.g_tip_distance():
  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))

def Laws.g_color_tty():
  ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))

def Laws.g_color_env():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==},
    ({==}, ({==}, ({==}, {==}))))))))))))

def Laws.g_color_flag():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))

def Laws.g_color_help():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_color_error():
  ({==}, {==})

def Laws.g_lint_lines():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==},
    ({==}, ({==}, ({==}, {==}))))))))))))

def Laws.g_lint_flag_default():
  ({==}, ({==}, ({==}, {==})))

# P10 and P11 follow eval_with's cases: lint, then the parse, then a
# built-in's page or the decoder's answer at the matched scope.
def p10_fault(-A: Type, f: Cli.Fault, cmd: Cli.Cmd,
    path: List<&2, String>, h: Cli.Host, argv: List<&2, String>) ->
    {Laws.p10_code(A, Cli.faulted(A, f, cmd, path, h, argv)) == True{}
      : Bool}:
  match f:
    case Cli.Bug{msg}: {==}
    case Cli.Usage{msg}: {==}

def p10_decoded(-A: Type, d: Cli.Dec(A), cmd: Cli.Cmd,
    path: List<&2, String>, h: Cli.Host, argv: List<&2, String>) ->
    {Laws.p10_code(A, Cli.decoded(A, d, cmd, path, h, argv)) == True{}
      : Bool}:
  match d:
    case Done{a}: {==}
    case Fail{f}: p10_fault(A, f, cmd, path, h, argv)

# completions and man show their page with code 0 and nothing on stderr.
def p10_accepted(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A),
    builtin: Maybe<&2, String>, +c: Cli.Cmd, +path: List<&2, String>,
    fields: List<&2, Cli.Field>, external: Maybe<&2, Cli.ExternalArgs>,
    h: Cli.Host, argv: List<&2, String>) ->
    {Laws.p10_code(A, Cli.eval_step(A, decode, Cli.outcome_accepted(builtin, c,
      path, fields, external), h, argv)) == True{} : Bool}:
  match builtin:
    case Some{name}: {==}
    case None{}:
      p10_decoded(A, decode(Cli.Matches{c, path, fields, external}), c,
        path, h, argv)

def p10_parse(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A),
    r: Cli.ParseResult, +c: Cli.Cmd, +h: Cli.Host,
    +argv: List<&2, String>) ->
    {Laws.p10_code(A, Cli.eval_step(A, decode, Cli.outcome_parse(r, c, h,
      argv), h, argv)) == True{} : Bool}:
  match r:
    case Cli.Accepted{+path, fields, external}:
      p10_accepted(A, decode,
        Cli.builtin_name(Cli.sub_at(path, Cli.cmd_items(c), None{})), c, path,
        fields, external, h, argv)
    case Cli.HelpRequested{path, long}: {==}
    case Cli.VersionRequested{}: {==}
    case Cli.SummaryRequired{}: {==}
    case Cli.Rejected{path, fault}: {==}

def p10_lint(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A),
    found: List<&2, Cli.Problem>, +c: Cli.Cmd, +h: Cli.Host,
    +argv: List<&2, String>) ->
    {Laws.p10_code(A, Cli.eval_step(A, decode, Cli.outcome_lint(found, c, h,
      argv), h, argv)) == True{} : Bool}:
  match found:
    case Nil{}: p10_parse(A, decode, Cli.parse(c, h, argv), c, h, argv)
    case p <> tail: {==}

def p10_cmd(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A), +c: Cli.Cmd,
    h: Cli.Host, argv: List<&2, String>) ->
    {Laws.p10_code(A, Cli.eval_with(A, decode, c, h, argv)) == True{}
      : Bool}:
  p10_lint(A, decode, Cli.problems(c), c, h, argv)

def Laws.p10(A, decode, c, h, argv):
  p10_cmd(A, decode, c, h, argv)

def p11_fault(-A: Type, f: Cli.Fault, cmd: Cli.Cmd,
    path: List<&2, String>, h: Cli.Host, argv: List<&2, String>) ->
    {Laws.p11_streams(A, Cli.faulted(A, f, cmd, path, h, argv)) == True{}
      : Bool}:
  match f:
    case Cli.Bug{msg}: {==}
    case Cli.Usage{msg}: {==}

def p11_decoded(-A: Type, d: Cli.Dec(A), cmd: Cli.Cmd,
    path: List<&2, String>, h: Cli.Host, argv: List<&2, String>) ->
    {Laws.p11_streams(A, Cli.decoded(A, d, cmd, path, h, argv)) == True{}
      : Bool}:
  match d:
    case Done{a}: {==}
    case Fail{f}: p11_fault(A, f, cmd, path, h, argv)

# completions and man show their page with code 0 and nothing on stderr.
def p11_accepted(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A),
    builtin: Maybe<&2, String>, +c: Cli.Cmd, +path: List<&2, String>,
    fields: List<&2, Cli.Field>, external: Maybe<&2, Cli.ExternalArgs>,
    h: Cli.Host, argv: List<&2, String>) ->
    {Laws.p11_streams(A, Cli.eval_step(A, decode, Cli.outcome_accepted(builtin, c,
      path, fields, external), h, argv)) == True{} : Bool}:
  match builtin:
    case Some{name}: {==}
    case None{}:
      p11_decoded(A, decode(Cli.Matches{c, path, fields, external}), c,
        path, h, argv)

def p11_parse(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A),
    r: Cli.ParseResult, +c: Cli.Cmd, +h: Cli.Host,
    +argv: List<&2, String>) ->
    {Laws.p11_streams(A, Cli.eval_step(A, decode, Cli.outcome_parse(r, c, h,
      argv), h, argv)) == True{} : Bool}:
  match r:
    case Cli.Accepted{+path, fields, external}:
      p11_accepted(A, decode,
        Cli.builtin_name(Cli.sub_at(path, Cli.cmd_items(c), None{})), c, path,
        fields, external, h, argv)
    case Cli.HelpRequested{path, long}: {==}
    case Cli.VersionRequested{}: {==}
    case Cli.SummaryRequired{}: {==}
    case Cli.Rejected{path, fault}: {==}

def p11_lint(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A),
    found: List<&2, Cli.Problem>, +c: Cli.Cmd, +h: Cli.Host,
    +argv: List<&2, String>) ->
    {Laws.p11_streams(A, Cli.eval_step(A, decode, Cli.outcome_lint(found, c, h,
      argv), h, argv)) == True{} : Bool}:
  match found:
    case Nil{}: p11_parse(A, decode, Cli.parse(c, h, argv), c, h, argv)
    case p <> tail: {==}

def p11_cmd(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A), +c: Cli.Cmd,
    h: Cli.Host, argv: List<&2, String>) ->
    {Laws.p11_streams(A, Cli.eval_with(A, decode, c, h, argv)) == True{}
      : Bool}:
  p11_lint(A, decode, Cli.problems(c), c, h, argv)

def Laws.p11(A, decode, c, h, argv):
  p11_cmd(A, decode, c, h, argv)

def Laws.eval_bridge(c, h, argv):
  ({==}, {==})

def p16_found(found: List<&2, Cli.Problem>, +c: Cli.Cmd, +h: Cli.Host,
    +argv: List<&2, String>) ->
    {Laws.through_linted(Cli.linted_found(found, c), c, h, argv)
      == Cli.outcome_lint(found, c, h, argv) : Cli.Outcome}:
  match found:
    case Nil{}: {==}
    case p <> tail: {==}

def Laws.p16(c, h, argv):
  p16_found(Cli.problems(c), c, h, argv)

def Laws.eval_with_step(A, decode, c, h, argv):
  {==}

def Laws.eval_linted_step(A, decode, l, h, argv):
  {==}

def p17_done(found: List<&2, Cli.Problem>, c: Cli.Cmd) ->
    {Result.is_done(&2, &2, List<&2, Cli.Problem>, Cli.Linted,
      Cli.linted_found(found, c))
      == List.is_empty(&2, Cli.Problem, found) : Bool}:
  match found:
    case Nil{}: {==}
    case p <> tail: {==}

def p17_problems(found: List<&2, Cli.Problem>, c: Cli.Cmd) ->
    {Laws.linted_problems(Cli.linted_found(found, c)) == found
      : List<&2, Cli.Problem>}:
  match found:
    case Nil{}: {==}
    case p <> tail: {==}

def Laws.p17(c):
  (p17_done(Cli.problems(c), c), p17_problems(Cli.problems(c), c))

def p10_on_linted(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A),
    l: Cli.Linted, +h: Cli.Host, +argv: List<&2, String>) ->
    {Laws.p10_code(A, Cli.eval_linted_with(A, decode, l, h, argv))
      == True{} : Bool}:
  match l:
    case Cli.Linted{+c}:
      p10_parse(A, decode, Cli.parse(c, h, argv), c, h, argv)

def Laws.p10_linted(A, decode, l, h, argv):
  p10_on_linted(A, decode, l, h, argv)

def p11_on_linted(-A: Type, decode: @+m: Cli.Matches -> Cli.Dec(A),
    l: Cli.Linted, +h: Cli.Host, +argv: List<&2, String>) ->
    {Laws.p11_streams(A, Cli.eval_linted_with(A, decode, l, h, argv))
      == True{} : Bool}:
  match l:
    case Cli.Linted{+c}:
      p11_parse(A, decode, Cli.parse(c, h, argv), c, h, argv)

def Laws.p11_linted(A, decode, l, h, argv):
  p11_on_linted(A, decode, l, h, argv)

def Laws.eval_linted_bridge(l, h, argv):
  ({==}, {==})

def Laws.g_lex_cluster_eval():
  {==}

def Laws.g_lex_values_eval():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))

def Laws.g_lex_end_eval():
  ({==}, {==})

def Laws.g_lex_count_eval():
  {==}

def Laws.g_lex_negation_eval():
  ({==}, {==})

def Laws.g_lex_bare_eval():
  {==}

def Laws.g_lex_errors_eval():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_lex_recovery_eval():
  {==}

def Laws.g_pos_variadic_eval():
  ({==}, ({==}, {==}))

def Laws.g_pos_cases_eval():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))

def Laws.g_sub_descent_eval():
  ({==}, ({==}, {==}))

def Laws.g_sub_alias_eval():
  {==}

def Laws.g_sub_help_eval():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_sub_scope_errors_eval():
  ({==}, ({==}, {==}))

def Laws.g_sub_external_eval():
  ({==}, {==})

def Laws.g_sub_missing_eval():
  ({==}, ({==}, {==}))

def Laws.g_sub_short_shadow_eval():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_val_strings_eval():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_val_nat_eval():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_val_u32_eval():
  ({==}, ({==}, {==}))

def Laws.g_val_f32_eval():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.g_val_bool_eval():
  ({==}, ({==}, {==}))

def Laws.g_val_one_of_eval():
  ({==}, {==})

def Laws.g_val_delim_eval():
  ({==}, {==})

def Laws.g_val_delim_typed_eval():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))

def Laws.g_src_env_eval():
  {==}

def Laws.g_src_empty_default_eval():
  {==}

def Laws.g_src_precedence_eval():
  ({==}, ({==}, {==}))

def Laws.g_src_invalid_eval():
  ({==}, {==})

def Laws.g_src_env_names_eval():
  ({==}, {==})

def Laws.g_rel_required_eval():
  ({==}, {==})

def Laws.g_rel_need_one_eval():
  ({==}, ({==}, {==}))

def Laws.g_rel_exclusive_eval():
  {==}

def Laws.g_rel_conflict_order_eval():
  ({==}, {==})

def Laws.g_rel_requires_eval():
  ({==}, {==})

def Laws.g_rel_defaults_eval():
  ({==}, {==})

def Laws.g_rel_global_groups_eval():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_err_decode():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==},
    {==})))))))))

def Laws.g_lint_exit():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_lint_required_sub_eval():
  ({==}, ({==}, {==}))

def Laws.g_vars():
  ({==}, ({==}, {==}))

def Laws.g_vars_env_names():
  ({==}, {==})

# A COLUMNS value as_nat accepts and that is not all zeroes sets the width
# to Nat.read's answer, whatever the TTYs say; s stays abstract, so the
# checker never builds the unary Nat.
def columns_used(+s: String, o: Bool, e: Bool, oc: U32, ec: U32,
    ok: {True{} == Cli.columns_ok(s) : Bool}) ->
    {Laws.width_of(Cli.probe(Laws.columns(s), o, e, oc, ec))
      == Maybe.default(&2, Nat, Nat.read(s), 0n) : Nat}:
  %ok : {Cli.width_or(Cli.columns_valid(_, s),
    Cli.nonzero(Cli.tty_columns(o, e, oc, ec), 80n))
    == Maybe.default(&2, Nat, Nat.read(s), 0n) : Nat}
  {==}

def Laws.g_host_probe():
  ({==}, ({==}, (columns_used("4294967296", False{}, False{}, 0, 0, {==}),
    ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==},
    {==})))))))))))

def Laws.g_act_exit():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.g_plan_pkg():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))

# M6: completions and man pages.

# The checker compares two strings with one nested call per char, so a
# golden script of a few thousand chars nears its stack limit, and whether
# it passes then varies from run to run. pieces cuts a string after each
# newline, and strings with equal pieces are equal (pieces_eq); the checker
# compares lists of pieces with one nested call per piece and per char of a
# piece. A Cut does the same for a step's out.

# s cut after each newline; the cut test need not hold of h for the pieces
# to concatenate back to s. cut comes first: --verdict's kernel binds the
# parameters before a match at q=2 and normalizes them, which would walk
# the pieces of the rest of s once per char.
def piece_push(cut: Bool, h: Char, r: List<&2, String>) -> List<&2, String>:
  match cut:
    case True{}: SCon{h, SNil{}} <> r
    case False{}: String.split.push(h, r)

def pieces(s: String) -> List<&2, String>:
  match s:
    case SNil{}: []
    case SCon{+h, t}: piece_push(Char.is_eq(h, '\n'), h, pieces(t))

def concat_push(h: Char, r: List<&2, String>) ->
    {String.concat(String.split.push(h, r)) == SCon{h, String.concat(r)} : String}:
  match r:
    case Nil{}: {==}
    case x <> rest: {==}

def concat_piece_push(+h: Char, +t: String,
    ih: {String.concat(pieces(t)) == t : String}, cut: Bool) ->
    {String.concat(piece_push(cut, h, pieces(t))) == SCon{h, t} : String}:
  match cut:
    case True{}:
      %ih : {String.concat(piece_push(True{}, h, pieces(t))) == SCon{h, _} : String}
      {==}
    case False{}:
      %ih : {String.concat(piece_push(False{}, h, pieces(t))) == SCon{h, _} : String}
      concat_push(h, pieces(t))

def concat_pieces(s: String) -> {String.concat(pieces(s)) == s : String}:
  match s:
    case SNil{}: {==}
    case SCon{+h, +t}: concat_piece_push(h, t, concat_pieces(t), Char.is_eq(h, '\n'))

# Strings with equal pieces are equal.
def pieces_eq(+x: String, +g: String, e: {pieces(x) == pieces(g) : List<&2, String>}) ->
    {x == g : String}:
  %concat_pieces(x) : {_ == g : String}
  %concat_pieces(g) : {String.concat(pieces(x)) == _ : String}
  %e : {String.concat(pieces(x)) == String.concat(_) : String}
  {==}

# A step with its out cut into pieces.
type Cut<-A: Type> is Type:
  CutGo{value: A, term: Cli.Term}
  CutQuit{code: U32, out: List<&2, String>, err: String}

def step_cut(-A: Type, s: Cli.Step<A>) -> Cut<A>:
  match s:
    case Cli.Go{value, term}: CutGo{value, term}
    case Cli.Quit{code, out, err}: CutQuit{code, pieces(out), err}

def step_join(-A: Type, c: Cut<A>) -> Cli.Step<A>:
  match c:
    case CutGo{value, term}: Cli.Go{value, term}
    case CutQuit{code, out, err}: Cli.Quit{code, String.concat(out), err}

def join_cut(-A: Type, s: Cli.Step<A>) ->
    {step_join(A, step_cut(A, s)) == s : Cli.Step<A>}:
  match s:
    case Cli.Go{value, term}: {==}
    case Cli.Quit{+code, +out, +err}:
      %concat_pieces(out) : {Cli.Quit{code, String.concat(pieces(out)), err}
        == Cli.Quit{code, _, err} : Cli.Step<A>}
      {==}

# Steps with equal cuts are equal.
def step_eq(-A: Type, run: Cli.Step<A>, g: Cli.Step<A>,
    e: {step_cut(A, run) == step_cut(A, g) : Cut<A>}) -> {run == g : Cli.Step<A>}:
  %join_cut(A, run) : {_ == g : Cli.Step<A>}
  %join_cut(A, g) : {step_join(A, step_cut(A, run)) == _ : Cli.Step<A>}
  %e : {step_join(A, step_cut(A, run)) == step_join(A, _) : Cli.Step<A>}
  {==}

def Laws.g_quote_models():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))))))))

def Laws.g_quote():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.g_comp_bash():
  pieces_eq(Cli.script(Demo.cli(), Cli.Bash{}), Laws.pkg_bash(), {==})

def Laws.g_comp_zsh():
  pieces_eq(Cli.script(Demo.cli(), Cli.Zsh{}), Laws.pkg_zsh(), {==})

def Laws.g_comp_fish():
  pieces_eq(Cli.script(Demo.cli(), Cli.Fish{}), Laws.pkg_fish(), {==})

def Laws.g_comp_quirks_bash():
  ({==}, pieces_eq(Cli.script(Laws.quirks(), Cli.Bash{}), Laws.quirks_bash(), {==}))

def Laws.g_comp_quirks_zsh():
  pieces_eq(Cli.script(Laws.quirks(), Cli.Zsh{}), Laws.quirks_zsh(), {==})

def Laws.g_comp_quirks_fish():
  pieces_eq(Cli.script(Laws.quirks(), Cli.Fish{}), Laws.quirks_fish(), {==})

def Laws.g_comp_launch_bash():
  ({==}, pieces_eq(Cli.script(Laws.launch(), Cli.Bash{}), Laws.launch_bash(), {==}))

def Laws.g_comp_launch_zsh():
  pieces_eq(Cli.script(Laws.launch(), Cli.Zsh{}), Laws.launch_zsh(), {==})

def Laws.g_comp_launch_fish():
  pieces_eq(Cli.script(Laws.launch(), Cli.Fish{}), Laws.launch_fish(), {==})

def Laws.g_man_pkg():
  pieces_eq(Cli.roff(Demo.cli(), []), Laws.pkg_man(), {==})

def Laws.g_man_add():
  pieces_eq(Cli.roff(Demo.cli(), ["add"]), Laws.add_man(), {==})

def Laws.g_man_path():
  (pieces_eq(Cli.roff(Demo.cli(), ["rm"]), Cli.roff(Demo.cli(), ["remove"]), {==}),
    (pieces_eq(Cli.roff(Demo.cli(), ["add", "x"]), Laws.add_man(), {==}),
      (pieces_eq(Cli.roff(Demo.cli(), ["nope", "add"]), Laws.pkg_man(), {==}),
        pieces_eq(Cli.roff(Demo.cli(), ["help"]), Laws.pkg_man(), {==}))))

def Laws.g_man_quirks():
  (pieces_eq(Cli.roff(Laws.quirks(), []), Laws.quirks_man(), {==}),
    (pieces_eq(Cli.roff(Laws.quirks(), ["rem", "add"]), Laws.quirks_add_man(), {==}),
      pieces_eq(Cli.roff(Laws.quirks(), ["remote", "prune"]), Laws.quirks_prune_man(), {==})))

def Laws.g_man_launch():
  pieces_eq(Cli.roff(Laws.launch(), []), Laws.launch_man(), {==})

def Laws.g_man_env_names():
  {==}

def Laws.g_eval_builtins():
  (step_eq(Demo.Action, Laws.pkg_run(Laws.host(), ["completions", "bash"]),
     Laws.shown(Demo.Action, Laws.pkg_bash()), {==}),
   (step_eq(Demo.Action, Laws.pkg_run(Laws.host(), ["completions", "zsh"]),
      Laws.shown(Demo.Action, Laws.pkg_zsh()), {==}),
    (step_eq(Demo.Action, Laws.pkg_run(Laws.tty(), ["--color=always", "completions", "fish"]),
       Laws.shown(Demo.Action, Laws.pkg_fish()), {==}),
     (step_eq(Bool, Cli.eval(~Bool, ~(+m => Cli.bug(Bool, "b")), Demo.cli(), Laws.host(),
        ["completions", "bash"]), Laws.shown(Bool, Laws.pkg_bash()), {==}),
      (step_eq(Bool, Cli.eval(~Bool, ~(+m => Cli.bug(Bool, "b")), Demo.cli(), Laws.host(),
         ["man", "add"]), Laws.shown(Bool, Laws.add_man()), {==}),
       (step_eq(Demo.Action, Laws.pkg_run(Laws.host(), ["man"]),
          Laws.shown(Demo.Action, Laws.pkg_man()), {==}),
        (step_eq(Demo.Action, Laws.pkg_run(Laws.tty(), ["-v", "man", "add"]),
           Laws.shown(Demo.Action, Laws.add_man()), {==}),
         (step_eq(Demo.Action, Laws.pkg_run(Laws.host(), ["man", "rm"]),
            Laws.shown(Demo.Action, Cli.roff(Demo.cli(), ["remove"])), {==}),
          (step_eq(Demo.Action, Laws.pkg_run(Laws.host(), ["man", "nope"]),
             Laws.shown(Demo.Action, Laws.pkg_man()), {==}),
           (step_eq(Demo.Action, Laws.pkg_run(Laws.host(), ["completions", "bash", "--help"]),
              Laws.shown(Demo.Action, Cli.help(Demo.cli(), ["completions"], True{}, Laws.host())), {==}),
            ({==}, ({==}, {==}))))))))))))

# P3, P4, P5, P6 and P15 go by induction on s, with a view of each char that
# tells the chars a quoter or reader treats apart from all others. The
# checker reduces a match on a char only where its bits are constructors, so
# each view's arms split c's bits as tools/charsplit.py prints them.

# P3: in quotes, the shell reads sh_body(s) then ' back as s.

# What the proof of P3 needs of a char other than ', \ and newline.
def ShOther(c: Char) -> Type:
  (@t: String -> {SCon{c, Cli.sh_body(t)} == Cli.sh_body(SCon{c, t}) : String}) &
  ((@x: String -> {Laws.put(c, Laws.sh_read(x, True{}))
      == Laws.sh_read(SCon{c, x}, True{}) : Maybe<&2, String>}) &
    (@x: String -> {Laws.put(Chr{92}, Laws.sh_read(SCon{c, x}, True{}))
      == Laws.sh_read(SCon{Chr{92}, SCon{c, x}}, True{}) : Maybe<&2, String>}))

def ShView(c: Char) -> Type:
  {Chr{39} == c : Char} | ({Chr{92} == c : Char} | ({Chr{10} == c : Char} | ShOther(c)))

# Arms: python3 tools/charsplit.py '(t => {==}, (x => {==}, x => {==}))' 39 92 10
def sh_view(c: Char) -> ShView(c):
  match c:
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inl{{==}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{True{}, WCon{False{}, _}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inl{{==}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inl{{==}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}:
      Inr{Inr{Inr{(t => {==}, (x => {==}, x => {==}))}}}

def sh_bs_cons(-c: Char, +u: String, v: ShView(c)) ->
    {Laws.put(Chr{92}, Laws.sh_read(String.append(Cli.sh_body(SCon{c, u}), "'"), True{}))
      == Laws.sh_read(SCon{Chr{92}, String.append(Cli.sh_body(SCon{c, u}), "'")}, True{})
      : Maybe<&2, String>}:
  match v:
    case Inl{e}:
      %e : {Laws.put(Chr{92}, Laws.sh_read(String.append(Cli.sh_body(SCon{_, u}), "'"), True{}))
        == Laws.sh_read(SCon{Chr{92}, String.append(Cli.sh_body(SCon{_, u}), "'")}, True{})
        : Maybe<&2, String>}
      {==}
    case Inr{Inl{e}}:
      %e : {Laws.put(Chr{92}, Laws.sh_read(String.append(Cli.sh_body(SCon{_, u}), "'"), True{}))
        == Laws.sh_read(SCon{Chr{92}, String.append(Cli.sh_body(SCon{_, u}), "'")}, True{})
        : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inl{e}}}:
      %e : {Laws.put(Chr{92}, Laws.sh_read(String.append(Cli.sh_body(SCon{_, u}), "'"), True{}))
        == Laws.sh_read(SCon{Chr{92}, String.append(Cli.sh_body(SCon{_, u}), "'")}, True{})
        : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{(body, (rd, rd_bs))}}}:
      %body(u) : {Laws.put(Chr{92}, Laws.sh_read(String.append(_, "'"), True{}))
        == Laws.sh_read(SCon{Chr{92}, String.append(_, "'")}, True{})
        : Maybe<&2, String>}
      rd_bs(String.append(Cli.sh_body(u), "'"))

# In quotes, a \ stands for itself whatever follows it.
def sh_bs_next(t: String) ->
    {Laws.put(Chr{92}, Laws.sh_read(String.append(Cli.sh_body(t), "'"), True{}))
      == Laws.sh_read(SCon{Chr{92}, String.append(Cli.sh_body(t), "'")}, True{})
      : Maybe<&2, String>}:
  match t:
    case SNil{}: {==}
    case SCon{c, u}: sh_bs_cons(c, u, sh_view(c))

def sh_in_cons(-c: Char, +t: String,
    ih: {Some{t} == Laws.sh_read(String.append(Cli.sh_body(t), "'"), True{})
      : Maybe<&2, String>},
    v: ShView(c)) ->
    {Some{SCon{c, t}} == Laws.sh_read(String.append(Cli.sh_body(SCon{c, t}), "'"), True{})
      : Maybe<&2, String>}:
  match v:
    case Inl{e}:
      %e : {Some{SCon{_, t}} == Laws.sh_read(String.append(Cli.sh_body(SCon{_, t}), "'"), True{})
        : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{39}, t}} == Laws.put(Chr{39}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inl{e}}:
      %e : {Some{SCon{_, t}} == Laws.sh_read(String.append(Cli.sh_body(SCon{_, t}), "'"), True{})
        : Maybe<&2, String>}
      %sh_bs_next(t) : {Some{SCon{Chr{92}, t}} == _ : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{92}, t}} == Laws.put(Chr{92}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inl{e}}}:
      %e : {Some{SCon{_, t}} == Laws.sh_read(String.append(Cli.sh_body(SCon{_, t}), "'"), True{})
        : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{10}, t}} == Laws.put(Chr{10}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{(body, (rd, rd_bs))}}}:
      %body(t) : {Some{SCon{c, t}} == Laws.sh_read(String.append(_, "'"), True{})
        : Maybe<&2, String>}
      %rd(String.append(Cli.sh_body(t), "'")) : {Some{SCon{c, t}} == _ : Maybe<&2, String>}
      %ih : {Some{SCon{c, t}} == Laws.put(c, _) : Maybe<&2, String>}
      {==}

def sh_in(s: String) ->
    {Some{s} == Laws.sh_read(String.append(Cli.sh_body(s), "'"), True{})
      : Maybe<&2, String>}:
  match s:
    case SNil{}: {==}
    case SCon{c, +t}: sh_in_cons(c, t, sh_in(t), sh_view(c))

def Laws.p3(s):
  Equal.sym(Maybe<&2, String>, Some{s}, Laws.Sh.unquote(Cli.Sh.quote(s)), sh_in(s))

# P4: in quotes, fish reads fish_body(s) then ' back as s.

# What the proof of P4 needs of a char other than ' and \.
def FishOther(c: Char) -> Type:
  (@t: String -> {SCon{c, Cli.fish_body(t)} == Cli.fish_body(SCon{c, t}) : String}) &
  (@x: String -> {Laws.put(c, Laws.fish_read(x, True{}))
    == Laws.fish_read(SCon{c, x}, True{}) : Maybe<&2, String>})

def FishView(c: Char) -> Type:
  {Chr{39} == c : Char} | ({Chr{92} == c : Char} | FishOther(c))

# Arms: python3 tools/charsplit.py '(t => {==}, x => {==})' 39 92
def fish_view(c: Char) -> FishView(c):
  match c:
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inl{{==}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{True{}, WCon{False{}, _}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{True{}, _}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inl{{==}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}:
      Inr{Inr{(t => {==}, x => {==})}}

def fish_in_cons(-c: Char, +t: String,
    ih: {Some{t} == Laws.fish_read(String.append(Cli.fish_body(t), "'"), True{})
      : Maybe<&2, String>},
    v: FishView(c)) ->
    {Some{SCon{c, t}} == Laws.fish_read(String.append(Cli.fish_body(SCon{c, t}), "'"), True{})
      : Maybe<&2, String>}:
  match v:
    case Inl{e}:
      %e : {Some{SCon{_, t}} == Laws.fish_read(String.append(Cli.fish_body(SCon{_, t}), "'"), True{})
        : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{39}, t}} == Laws.put(Chr{39}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inl{e}}:
      %e : {Some{SCon{_, t}} == Laws.fish_read(String.append(Cli.fish_body(SCon{_, t}), "'"), True{})
        : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{92}, t}} == Laws.put(Chr{92}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{(body, rd)}}:
      %body(t) : {Some{SCon{c, t}} == Laws.fish_read(String.append(_, "'"), True{})
        : Maybe<&2, String>}
      %rd(String.append(Cli.fish_body(t), "'")) : {Some{SCon{c, t}} == _ : Maybe<&2, String>}
      %ih : {Some{SCon{c, t}} == Laws.put(c, _) : Maybe<&2, String>}
      {==}

def fish_in(s: String) ->
    {Some{s} == Laws.fish_read(String.append(Cli.fish_body(s), "'"), True{})
      : Maybe<&2, String>}:
  match s:
    case SNil{}: {==}
    case SCon{c, +t}: fish_in_cons(c, t, fish_in(t), fish_view(c))

def Laws.p4(s):
  Equal.sym(Maybe<&2, String>, Some{s}, Laws.Fish.unquote(Cli.Fish.quote(s)), fish_in(s))

# P5: Zsh.unesc reads each \c of Zsh.esc(s) as c.

# What the proof of P5 needs of a char other than \, [, ] and :.
def ZshOther(c: Char) -> Type:
  (@t: String -> {SCon{c, Cli.Zsh.esc(t)} == Cli.Zsh.esc(SCon{c, t}) : String}) &
  (@x: String -> {Laws.put(c, Laws.Zsh.unesc(x)) == Laws.Zsh.unesc(SCon{c, x})
    : Maybe<&2, String>})

def ZshView(c: Char) -> Type:
  {Chr{92} == c : Char} | ({Chr{91} == c : Char} |
    ({Chr{93} == c : Char} | ({Chr{58} == c : Char} | ZshOther(c))))

# Arms: python3 tools/charsplit.py '(t => {==}, x => {==})' 92 91 93 58
def zsh_view(c: Char) -> ZshView(c):
  match c:
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inl{{==}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inl{{==}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inl{{==}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inl{{==}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}:
      Inr{Inr{Inr{Inr{(t => {==}, x => {==})}}}}

def zsh_in_cons(-c: Char, +t: String,
    ih: {Some{t} == Laws.Zsh.unesc(Cli.Zsh.esc(t)) : Maybe<&2, String>},
    v: ZshView(c)) ->
    {Some{SCon{c, t}} == Laws.Zsh.unesc(Cli.Zsh.esc(SCon{c, t})) : Maybe<&2, String>}:
  match v:
    case Inl{e}:
      %e : {Some{SCon{_, t}} == Laws.Zsh.unesc(Cli.Zsh.esc(SCon{_, t})) : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{92}, t}} == Laws.put(Chr{92}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inl{e}}:
      %e : {Some{SCon{_, t}} == Laws.Zsh.unesc(Cli.Zsh.esc(SCon{_, t})) : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{91}, t}} == Laws.put(Chr{91}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inl{e}}}:
      %e : {Some{SCon{_, t}} == Laws.Zsh.unesc(Cli.Zsh.esc(SCon{_, t})) : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{93}, t}} == Laws.put(Chr{93}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{Inl{e}}}}:
      %e : {Some{SCon{_, t}} == Laws.Zsh.unesc(Cli.Zsh.esc(SCon{_, t})) : Maybe<&2, String>}
      %ih : {Some{SCon{Chr{58}, t}} == Laws.put(Chr{58}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{Inr{(body, rd)}}}}:
      %body(t) : {Some{SCon{c, t}} == Laws.Zsh.unesc(_) : Maybe<&2, String>}
      %rd(Cli.Zsh.esc(t)) : {Some{SCon{c, t}} == _ : Maybe<&2, String>}
      %ih : {Some{SCon{c, t}} == Laws.put(c, _) : Maybe<&2, String>}
      {==}

def zsh_in(s: String) -> {Some{s} == Laws.Zsh.unesc(Cli.Zsh.esc(s)) : Maybe<&2, String>}:
  match s:
    case SNil{}: {==}
    case SCon{c, +t}: zsh_in_cons(c, t, zsh_in(t), zsh_view(c))

def Laws.p5(s):
  Equal.sym(Maybe<&2, String>, Some{s}, Laws.Zsh.unesc(Cli.Zsh.esc(s)), zsh_in(s))

# P6 and P15: roff_body(s, b) for a line start b, read from the same b.

# What the proofs of P6 and P15 need of a char that roff_body neither
# escapes nor guards at a line start, and that is not a newline.
def RoffOther(c: Char) -> Type:
  (@b: Bool -> @t: String -> {SCon{c, Cli.roff_body(t, False{})}
    == Cli.roff_body(SCon{c, t}, b) : String}) &
  ((@b: Bool -> @x: String -> {Laws.put(c, Laws.roff_read(x, False{}))
      == Laws.roff_read(SCon{c, x}, b) : Maybe<&2, String>}) &
    (@b: Bool -> @x: String -> {Laws.no_request(x, False{})
      == Laws.no_request(SCon{c, x}, b) : Bool}))

def RoffView(c: Char) -> Type:
  {Chr{46} == c : Char} | ({Chr{32} == c : Char} | ({Chr{10} == c : Char} |
    ({Chr{92} == c : Char} | ({Chr{45} == c : Char} | ({Chr{34} == c : Char} |
      ({Chr{39} == c : Char} | ({Chr{96} == c : Char} | RoffOther(c))))))))

# Arms: python3 tools/charsplit.py '(b => t => {==}, (b => x => {==}, b => x => {==}))' 46 32 10 92 45 34 39 96
def roff_char_view(c: Char) -> RoffView(c):
  match c:
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inl{{==}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inl{{==}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inl{{==}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inl{{==}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inl{{==}}}}}}}
    case Chr{U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inl{{==}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{{==}}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      Inr{Inl{{==}}}
    case Chr{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}}}}}:
      Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(b => t => {==}, (b => x => {==}, b => x => {==}))}}}}}}}}

def no_request_cons(-c: Char, +t: String,
    ih: @n: Bool -> {Laws.no_request(Cli.roff_body(t, n), n) == True{} : Bool},
    v: RoffView(c), +b: Bool) ->
    {Laws.no_request(Cli.roff_body(SCon{c, t}, b), b) == True{} : Bool}:
  match v:
    case Inl{e}:
      match b:
        case True{}:
          %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, True{}), True{}) == True{} : Bool}
          ih(False{})
        case False{}:
          %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, False{}), False{}) == True{} : Bool}
          ih(False{})
    case Inr{Inl{e}}:
      match b:
        case True{}:
          %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, True{}), True{}) == True{} : Bool}
          ih(False{})
        case False{}:
          %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, False{}), False{}) == True{} : Bool}
          ih(False{})
    case Inr{Inr{Inl{e}}}:
      %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, b), b) == True{} : Bool}
      ih(True{})
    case Inr{Inr{Inr{Inl{e}}}}:
      %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, b), b) == True{} : Bool}
      ih(False{})
    case Inr{Inr{Inr{Inr{Inl{e}}}}}:
      %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, b), b) == True{} : Bool}
      ih(False{})
    case Inr{Inr{Inr{Inr{Inr{Inl{e}}}}}}:
      %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, b), b) == True{} : Bool}
      ih(False{})
    case Inr{Inr{Inr{Inr{Inr{Inr{Inl{e}}}}}}}:
      %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, b), b) == True{} : Bool}
      ih(False{})
    case Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{e}}}}}}}}:
      %e : {Laws.no_request(Cli.roff_body(SCon{_, t}, b), b) == True{} : Bool}
      ih(False{})
    case Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(body, (rd, nr))}}}}}}}}:
      %body(b, t) : {Laws.no_request(_, b) == True{} : Bool}
      %nr(b, Cli.roff_body(t, False{})) : {_ == True{} : Bool}
      ih(False{})

def no_request_in(s: String, b: Bool) ->
    {Laws.no_request(Cli.roff_body(s, b), b) == True{} : Bool}:
  match s:
    case SNil{}: {==}
    case SCon{c, +t}: no_request_cons(c, t, n => no_request_in(t, n), roff_char_view(c), b)

def Laws.p6(s):
  no_request_in(s, True{})

def roff_in_cons(-c: Char, +t: String,
    ih: @n: Bool -> {Some{t} == Laws.roff_read(Cli.roff_body(t, n), n)
      : Maybe<&2, String>},
    v: RoffView(c), +b: Bool) ->
    {Some{SCon{c, t}} == Laws.roff_read(Cli.roff_body(SCon{c, t}, b), b)
      : Maybe<&2, String>}:
  match v:
    case Inl{e}:
      match b:
        case True{}:
          %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, True{}), True{})
            : Maybe<&2, String>}
          %ih(False{}) : {Some{SCon{Chr{46}, t}} == Laws.put(Chr{46}, _) : Maybe<&2, String>}
          {==}
        case False{}:
          %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, False{}), False{})
            : Maybe<&2, String>}
          %ih(False{}) : {Some{SCon{Chr{46}, t}} == Laws.put(Chr{46}, _) : Maybe<&2, String>}
          {==}
    case Inr{Inl{e}}:
      match b:
        case True{}:
          %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, True{}), True{})
            : Maybe<&2, String>}
          %ih(False{}) : {Some{SCon{Chr{32}, t}} == Laws.put(Chr{32}, _) : Maybe<&2, String>}
          {==}
        case False{}:
          %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, False{}), False{})
            : Maybe<&2, String>}
          %ih(False{}) : {Some{SCon{Chr{32}, t}} == Laws.put(Chr{32}, _) : Maybe<&2, String>}
          {==}
    case Inr{Inr{Inl{e}}}:
      %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, b), b)
        : Maybe<&2, String>}
      %ih(True{}) : {Some{SCon{Chr{10}, t}} == Laws.put(Chr{10}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{Inl{e}}}}:
      %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, b), b)
        : Maybe<&2, String>}
      %ih(False{}) : {Some{SCon{Chr{92}, t}} == Laws.put(Chr{92}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{Inr{Inl{e}}}}}:
      %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, b), b)
        : Maybe<&2, String>}
      %ih(False{}) : {Some{SCon{Chr{45}, t}} == Laws.put(Chr{45}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{Inr{Inr{Inl{e}}}}}}:
      %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, b), b)
        : Maybe<&2, String>}
      %ih(False{}) : {Some{SCon{Chr{34}, t}} == Laws.put(Chr{34}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{Inr{Inr{Inr{Inl{e}}}}}}}:
      %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, b), b)
        : Maybe<&2, String>}
      %ih(False{}) : {Some{SCon{Chr{39}, t}} == Laws.put(Chr{39}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{e}}}}}}}}:
      %e : {Some{SCon{_, t}} == Laws.roff_read(Cli.roff_body(SCon{_, t}, b), b)
        : Maybe<&2, String>}
      %ih(False{}) : {Some{SCon{Chr{96}, t}} == Laws.put(Chr{96}, _) : Maybe<&2, String>}
      {==}
    case Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{(body, (rd, nr))}}}}}}}}:
      %body(b, t) : {Some{SCon{c, t}} == Laws.roff_read(_, b) : Maybe<&2, String>}
      %rd(b, Cli.roff_body(t, False{})) : {Some{SCon{c, t}} == _ : Maybe<&2, String>}
      %ih(False{}) : {Some{SCon{c, t}} == Laws.put(c, _) : Maybe<&2, String>}
      {==}

def roff_in(s: String, b: Bool) ->
    {Some{s} == Laws.roff_read(Cli.roff_body(s, b), b) : Maybe<&2, String>}:
  match s:
    case SNil{}: {==}
    case SCon{c, +t}: roff_in_cons(c, t, n => roff_in(t, n), roff_char_view(c), b)

def Laws.p15(s):
  Equal.sym(Maybe<&2, String>, Some{s}, Laws.Roff.unesc(Cli.Roff.esc(s)), roff_in(s, True{}))
