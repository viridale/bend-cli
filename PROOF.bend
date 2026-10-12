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

def string_cmp_refl(s: String) ->
    {((s, s), EQ{}) == String.cmp(s, s) : (String & String) & Cmp}:
  match s:
    case SNil{}: {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          match x:
            case U32{w}:
              %word_cmp_refl(32n, w) :
                {((SCon{Chr{U32{w}}, t}, SCon{Chr{U32{w}}, t}), EQ{})
                  == String.cmp.fin(t, t,
                    ((Chr{U32{w}}, Chr{U32{w}}), _))
                  : (String & String) & Cmp}
              %string_cmp_refl(t) :
                {((SCon{Chr{U32{w}}, t}, SCon{Chr{U32{w}}, t}), EQ{})
                  == String.cmp.rec(Chr{U32{w}}, Chr{U32{w}}, _)
                  : (String & String) & Cmp}
              {==}

def string_eq_refl(s: String) -> {String.eq(s, s) == True{} : Bool}:
  %string_cmp_refl(s) :
    {Cmp.is_eq(Pair.snd(String & String, Cmp, _)) == True{} : Bool}
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
        case Cli.Scope{path, items, globals}:
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
        case Cli.Scope{path, items, globals}:
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

def or_false_left(b: Bool, c: Bool,
    e: {False{} == Bool.or(b, c) : Bool}) -> {False{} == b : Bool}:
  match b:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, false_true_absurd(e))
    case False{}: {==}

def or_false_right(b: Bool, c: Bool,
    e: {False{} == Bool.or(b, c) : Bool}) -> {False{} == c : Bool}:
  match b:
    case True{}:
      Empty.absurd({False{} == c : Bool}, false_true_absurd(e))
    case False{}: e

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
          %or_false_left(String.eq(t, "--"),
            List.contains(~String, ~String.eq, rest, "--"), free) :
            {Laws.p9_trace(q, post, Cli.scan_trace(Cli.scan_go(
              List.append(&2, String, rest, "--" <> post),
              Cli.scan_open(_, state, t)))) == True{} : Bool}
          p9_before(rest, q, post, Cli.scan_token(t, state), clear,
            or_false_right(String.eq(t, "--"),
              List.contains(~String, ~String.eq, rest, "--"), free))
        case Cli.Fetch{state, info}:
          p9_before(rest, q, post, Cli.scan_fetch(state, info, t), clear,
            or_false_right(String.eq(t, "--"),
              List.contains(~String, ~String.eq, rest, "--"), free))
        case Cli.Operands{state, ended}:
          p9_before(rest, q, post,
            Cli.Operands{Cli.scan_operand(state, t), ended}, clear,
            or_false_right(String.eq(t, "--"),
              List.contains(~String, ~String.eq, rest, "--"), free))
        case Cli.Capture{state, name}:
          p9_unended(q, post, Cli.scan_external(state, name,
            t <> List.append(&2, String, rest, "--" <> post)), clear)
        case Cli.Closed{tail}:
          p9_before(rest, q, post, Cli.Closed{Cli.scan_tail(tail, t)},
            clear, or_false_right(String.eq(t, "--"),
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

def keep_pick(hit: Bool, keys: List<&2, String>, +all: List<&2, String>,
    +key: String, c: Cli.Cmd, +path: List<&2, String>, +m1: Cli.Matches,
    +m2: Cli.Matches,
    rest: {Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
      Cli.find_by_key(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
        key), all, c, path, m1)) ==
      Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
        Cli.find_by_key(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
          key), all, c, path, m2)) : Maybe<&2, String>}) ->
    {Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
      Bool.pick(Maybe<Cli.Call(Cli.Matches)>, hit, Some{+n => Cli.keep(n)},
        Cli.find_by_key(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
          key)), all, c, path, m1)) ==
      Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
        Bool.pick(Maybe<Cli.Call(Cli.Matches)>, hit, Some{+n => Cli.keep(n)},
          Cli.find_by_key(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
            key)), all, c, path, m2)) : Maybe<&2, String>}:
  match hit c:
    case True{} Cli.Cmd{name, about, items}:
      call_same(Cli.non_command(all, items), m1, m2)
    case False{} _: rest

def keep_ok(keys: List<&2, String>, +all: List<&2, String>, +key: String,
    +c: Cli.Cmd, +path: List<&2, String>, +m1: Cli.Matches,
    +m2: Cli.Matches) ->
    {Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
      Cli.find_by_key(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
        key), all, c, path, m1)) ==
      Laws.bug_of(Cli.Matches, Cli.route_found(Cli.Matches,
        Cli.find_by_key(&1, Cli.Call(Cli.Matches), keys, keep_calls(keys),
          key), all, c, path, m2)) : Maybe<&2, String>}:
  match keys:
    case Nil{}:
      match c:
        case Cli.Cmd{name, about, items}: {==}
    case +head <> +tail:
      keep_pick(String.eq(head, key), tail, all, key, c, path, m1, m2,
        keep_ok(tail, all, key, c, path, m1, m2))

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

def or_false_head(b: Bool, c: Bool, e: {Bool.or(b, c) == False{} : Bool}) ->
    {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false_absurd(e))
    case False{}: {==}

def or_false_tail(b: Bool, c: Bool, e: {Bool.or(b, c) == False{} : Bool}) ->
    {c == False{} : Bool}:
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
        step_open(s, token, open, or_false_head(String.eq(token, "--"),
          List.contains(~String, ~String.eq, tail, "--"), clear)),
        or_false_tail(String.eq(token, "--"),
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

def Laws.g_help_usage():
  ({==}, {==})

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
