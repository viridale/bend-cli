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

# P18 text: String.eq is String.cmp's result at EQ, which a mismatched char
# fixes, as it fixes same_go's flag at False.
def same_go_false(a: String, b: String) ->
    {Cli.same_go(a, b, False{}) == False{} : Bool}:
  match a b:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{h, t}: {==}
    case SCon{h, t} SNil{}: {==}
    case SCon{x, xt} SCon{y, yt}: {==}

def cmp_rec_snd(h1: Char, h2: Char, rr: (String & String) & Cmp) ->
    {Pair.snd(String & String, Cmp, rr)
      == Pair.snd(String & String, Cmp, String.cmp.rec(h1, h2, rr)) : Cmp}:
  match rr:
    case (ts, r):
      match ts:
        case (t1, t2): {==}

def text_step(+xt: String, +yt: String, h1: Char, h2: Char, c: Cmp) ->
    {Cli.same_go(xt, yt, True{}) == String.eq(xt, yt) : Bool} ->
    {Cli.same_go(xt, yt, Cmp.is_eq(c)) == Cmp.is_eq(Pair.snd(String & String,
      Cmp, String.cmp.fin(xt, yt, ((h1, h2), c)))) : Bool}:
  match c:
    case LT{}: ih => same_go_false(xt, yt)
    case EQ{}:
      ih =>
        %cmp_rec_snd(h1, h2, String.cmp(xt, yt)) :
          {Cli.same_go(xt, yt, True{}) == Cmp.is_eq(_) : Bool}
        ih
    case GT{}: ih => same_go_false(xt, yt)

def Laws.p18_text(a, b):
  match a b:
    case SNil{} SNil{}: {==}
    case SNil{} SCon{h, t}: {==}
    case SCon{h, t} SNil{}: {==}
    case SCon{Chr{+p}, +xt} SCon{Chr{+q}, +yt}:
      text_step(xt, yt, Chr{p}, Chr{q}, U32.cmp(p, q),
        Laws.p18_text(xt, yt))

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

# Arms: python3 tools/ctorarms.py --prefix Cli. --skip Arg cli.bend Item '$P <> tail' 'global_comm(tail)'
def global_comm(items: List<&2, Cli.Item>) ->
    {Cli.spec_items(Cli.global_items(items))
      == Cli.global_spec(Cli.spec_items(items)) : List<&2, Cli.SpecItem>}:
  match items:
    case Nil{}: {==}
    case Cli.Arg{+usage, +help, +attrs} <> +tail:
      %global_comm(tail) :
        {Cli.spec_items(Bool.pick(List<&2, Cli.Item>, Cli.has_global(attrs),
          Cli.Arg{usage, help, attrs} <> Cli.global_items(tail),
          Cli.global_items(tail)))
          == Bool.pick(List<&2, Cli.SpecItem>,
            Cli.has_global(Cli.info_attrs(Cli.arg_info(usage, attrs))),
            Cli.SpecArg{Cli.arg_info(usage, attrs)} <> _, _)
          : List<&2, Cli.SpecItem>}
      %attrs_parsed(Cli.parse_usage(usage), usage, attrs) :
        {Cli.spec_items(Bool.pick(List<&2, Cli.Item>, Cli.has_global(attrs),
          Cli.Arg{usage, help, attrs} <> Cli.global_items(tail),
          Cli.global_items(tail)))
          == Bool.pick(List<&2, Cli.SpecItem>, Cli.has_global(_),
            Cli.SpecArg{Cli.arg_info(usage, attrs)}
              <> Cli.spec_items(Cli.global_items(tail)),
            Cli.spec_items(Cli.global_items(tail)))
          : List<&2, Cli.SpecItem>}
      global_pick(Cli.has_global(attrs), usage, help, attrs,
        Cli.global_items(tail))
    case Cli.Sub{x0, x1, x2} <> tail: global_comm(tail)
    case Cli.Version{x0} <> tail: global_comm(tail)
    case Cli.Alias{x0} <> tail: global_comm(tail)
    case Cli.Hidden{} <> tail: global_comm(tail)
    case Cli.Example{x0, x1} <> tail: global_comm(tail)
    case Cli.After{x0} <> tail: global_comm(tail)
    case Cli.SubOptional{} <> tail: global_comm(tail)
    case Cli.External{} <> tail: global_comm(tail)
    case Cli.Exclusive{x0} <> tail: global_comm(tail)
    case Cli.NeedOne{x0} <> tail: global_comm(tail)
    case Cli.Id{x0} <> tail: global_comm(tail)
    case Cli.Required{} <> tail: global_comm(tail)
    case Cli.AttrDefault{x0} <> tail: global_comm(tail)
    case Cli.AttrEnv{x0} <> tail: global_comm(tail)
    case Cli.Global{} <> tail: global_comm(tail)
    case Cli.Heading{x0} <> tail: global_comm(tail)
    case Cli.As{x0} <> tail: global_comm(tail)
    case Cli.OneOf{x0} <> tail: global_comm(tail)
    case Cli.Delim{x0} <> tail: global_comm(tail)
    case Cli.Hyphen{} <> tail: global_comm(tail)
    case Cli.Rest{} <> tail: global_comm(tail)
    case Cli.Bare{x0} <> tail: global_comm(tail)
    case Cli.Conflicts{x0} <> tail: global_comm(tail)
    case Cli.Requires{x0} <> tail: global_comm(tail)
    case Cli.Group{x0} <> tail: global_comm(tail)
    case Cli.Builtin{} <> tail: global_comm(tail)

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
    case Cli.Alias{name} <> tail:
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
    case +n <> t None{}:
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
      %contains_append(t, ys, q) :
        {Bool.or(Bool.or(String.eq(x, q),
          List.contains(~String, ~String.eq, t, q)),
          List.contains(~String, ~String.eq, ys, q))
          == Bool.or(String.eq(x, q), _) : Bool}
      or_assoc(String.eq(x, q), List.contains(~String, ~String.eq, t, q),
        List.contains(~String, ~String.eq, ys, q))

def or_false(x: Bool) -> {x == Bool.or(x, False{}) : Bool}:
  match x:
    case True{}: {==}
    case False{}: {==}

def sym_or_false(+q: String, +s: String) ->
    {String.eq(q, s) == Bool.or(String.eq(s, q), False{}) : Bool}:
  %str_sym(s, q) : {_ == Bool.or(String.eq(s, q), False{}) : Bool}
  or_false(String.eq(s, q))

def nonempty_contains(s: String, +q: String) ->
    {Bool.and(Bool.not(String.is_empty(s)), String.eq(q, s))
      == List.contains(~String, ~String.eq, Cli.nonempty_name(s), q)
      : Bool}:
  match s:
    case SNil{}: {==}
    case SCon{+h, +t}: sym_or_false(q, SCon{h, t})

def neg_contains(g: Bool, l: Bool, +nl: String, +q: String) ->
    {Bool.and(g, Bool.and(l, String.eq(q, nl)))
      == List.contains(~String, ~String.eq,
        Bool.pick(List<&2, String>, Bool.and(g, l), [nl], []), q) : Bool}:
  match g l:
    case True{} True{}: sym_or_false(q, nl)
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
            Cli.spec_node(children, _)}, Cli.Enter{name} <> events, resting,
            0n, external, issue}}),
        Cli.scope_args(tail, children, List.append(&2, Cli.Item,
          Cli.global_items(items), globals)), id)
      ih(List.append(&2, String, p, [name]), Cli.Enter{name} <> events,
        children)

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

def Laws.g_err_decode():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==},
    {==})))))))))

def Laws.g_lint_exit():
  ({==}, ({==}, ({==}, {==})))

def Laws.g_vars():
  ({==}, ({==}, {==}))

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
