# Purpose: pure command definitions, validation, and text rendering for Bend CLIs.
# Expected output: ALL PROOFS CHECK.
# Run: bend cli.bend --check-only

import Base

type Style is Data:
  Bold{}
  Dim{}
  Under{}
  Red{}
  Green{}
  Yellow{}
  Blue{}
  Magenta{}
  Cyan{}

type Segment is Data:
  Segment{text: String, styles: List<&2, Style>}

def style_code(style: Style) -> String:
  match style:
    case Bold{}: "1"
    case Dim{}: "2"
    case Under{}: "4"
    case Red{}: "31"
    case Green{}: "32"
    case Yellow{}: "33"
    case Blue{}: "34"
    case Magenta{}: "35"
    case Cyan{}: "36"

def style_codes_tail(styles: List<&2, Style>) -> String:
  match styles:
    case Nil{}: ""
    case h <> t:
      String.append(";", String.append(style_code(h), style_codes_tail(t)))

def style_codes(styles: List<&2, Style>) -> String:
  match styles:
    case Nil{}: ""
    case h <> t:
      String.append(style_code(h), style_codes_tail(t))

def paint(on: Bool, styles: List<&2, Style>, text: String) -> String:
  match on styles:
    case False{} _:
      text
    case True{} Nil{}:
      text
    case True{} h <> t:
      String.append("\u{1B}[",
        String.append(style_codes(h <> t),
          String.append("m", String.append(text, "\u{1B}[0m"))))

def emit_go(segments: List<&2, Segment>, +on: Bool) -> String:
  match segments:
    case Nil{}:
      ""
    case h <> t:
      match h:
        case Segment{text, styles}:
          String.append(paint(on, styles, text), emit_go(t, on))

def emit(on: Bool, segments: List<&2, Segment>) -> String:
  emit_go(segments, on)

def sgr_body_char(+c: Char) -> Bool:
  Bool.or(Char.is_digit(c), Char.is_eq(c, ';'))

type StripState is Data:
  StripPlain{out: String}
  StripEsc{out: String}
  StripBody{out: String, pending: String}

def strip_fuel(fuel: Nat, state: StripState, s: String) -> String:
  match fuel:
    case 0n:
      s
    case 1n+p:
      match state:
        case StripPlain{+out}:
          match s:
            case SNil{}:
              out
            case SCon{+head, tail}:
              strip_fuel(p, Bool.pick(StripState,
                Char.is_eq(head, '\u{1B}'), StripEsc{out},
                StripPlain{String.append(out, Char.show(head))}), tail)
        case StripEsc{+out}:
          match s:
            case SNil{}:
              String.append(out, "\u{1B}")
            case SCon{head, tail}:
              match head:
                case Chr{91}:
                  strip_fuel(p, StripBody{out, "\u{1B}["}, tail)
                case Chr{27}:
                  strip_fuel(p, StripEsc{String.append(out, "\u{1B}")}, tail)
                case _:
                  strip_fuel(p, StripPlain{String.append(out,
                    String.append("\u{1B}", Char.show(head)))}, tail)
        case StripBody{+out, +pending}:
          match s:
            case SNil{}:
              String.append(out, pending)
            case SCon{+head, tail}:
              match head:
                case Chr{109}:
                  strip_fuel(p, StripPlain{out}, tail)
                case Chr{27}:
                  strip_fuel(p, StripEsc{String.append(out, pending)}, tail)
                case _:
                  strip_fuel(p, Bool.pick(StripState, sgr_body_char(head),
                    StripBody{out, String.append(pending, Char.show(head))},
                    StripPlain{String.append(out,
                      String.append(pending, Char.show(head)))}), tail)

def strip(+s: String) -> String:
  strip_fuel(Nat.add(1n, String.length(s)), StripPlain{""}, s)

type CodeRange is Data:
  CodeRange{lo: U32, hi: U32}

def contains_range(ranges: List<&2, CodeRange>, +code: U32) -> Bool:
  match ranges:
    case Nil{}:
      False{}
    case CodeRange{lo, hi} <> tail:
      Bool.or(Bool.and(U32.is_ge(code, lo), U32.is_le(code, hi)),
        contains_range(tail, code))

# Unicode 15.1 East Asian Wide and Fullwidth ranges, including reserved ranges.
# Source: https://www.unicode.org/Public/15.1.0/ucd/EastAsianWidth.txt
def unicode_is_wide(code: U32) -> Bool:
  contains_range([
    CodeRange{4352, 4447},
    CodeRange{8986, 8987},
    CodeRange{9001, 9002},
    CodeRange{9193, 9196},
    CodeRange{9200, 9200},
    CodeRange{9203, 9203},
    CodeRange{9725, 9726},
    CodeRange{9748, 9749},
    CodeRange{9800, 9811},
    CodeRange{9855, 9855},
    CodeRange{9875, 9875},
    CodeRange{9889, 9889},
    CodeRange{9898, 9899},
    CodeRange{9917, 9918},
    CodeRange{9924, 9925},
    CodeRange{9934, 9934},
    CodeRange{9940, 9940},
    CodeRange{9962, 9962},
    CodeRange{9970, 9971},
    CodeRange{9973, 9973},
    CodeRange{9978, 9978},
    CodeRange{9981, 9981},
    CodeRange{9989, 9989},
    CodeRange{9994, 9995},
    CodeRange{10024, 10024},
    CodeRange{10060, 10060},
    CodeRange{10062, 10062},
    CodeRange{10067, 10069},
    CodeRange{10071, 10071},
    CodeRange{10133, 10135},
    CodeRange{10160, 10160},
    CodeRange{10175, 10175},
    CodeRange{11035, 11036},
    CodeRange{11088, 11088},
    CodeRange{11093, 11093},
    CodeRange{11904, 11929},
    CodeRange{11931, 12019},
    CodeRange{12032, 12245},
    CodeRange{12272, 12350},
    CodeRange{12353, 12438},
    CodeRange{12441, 12543},
    CodeRange{12549, 12591},
    CodeRange{12593, 12686},
    CodeRange{12688, 12771},
    CodeRange{12783, 12830},
    CodeRange{12832, 12871},
    CodeRange{12880, 19903},
    CodeRange{19968, 42124},
    CodeRange{42128, 42182},
    CodeRange{43360, 43388},
    CodeRange{44032, 55203},
    CodeRange{63744, 64255},
    CodeRange{65040, 65049},
    CodeRange{65072, 65106},
    CodeRange{65108, 65126},
    CodeRange{65128, 65131},
    CodeRange{65281, 65376},
    CodeRange{65504, 65510},
    CodeRange{94176, 94180},
    CodeRange{94192, 94193},
    CodeRange{94208, 100343},
    CodeRange{100352, 101589},
    CodeRange{101632, 101640},
    CodeRange{110576, 110579},
    CodeRange{110581, 110587},
    CodeRange{110589, 110590},
    CodeRange{110592, 110882},
    CodeRange{110898, 110898},
    CodeRange{110928, 110930},
    CodeRange{110933, 110933},
    CodeRange{110948, 110951},
    CodeRange{110960, 111355},
    CodeRange{126980, 126980},
    CodeRange{127183, 127183},
    CodeRange{127374, 127374},
    CodeRange{127377, 127386},
    CodeRange{127488, 127490},
    CodeRange{127504, 127547},
    CodeRange{127552, 127560},
    CodeRange{127568, 127569},
    CodeRange{127584, 127589},
    CodeRange{127744, 127776},
    CodeRange{127789, 127797},
    CodeRange{127799, 127868},
    CodeRange{127870, 127891},
    CodeRange{127904, 127946},
    CodeRange{127951, 127955},
    CodeRange{127968, 127984},
    CodeRange{127988, 127988},
    CodeRange{127992, 128062},
    CodeRange{128064, 128064},
    CodeRange{128066, 128252},
    CodeRange{128255, 128317},
    CodeRange{128331, 128334},
    CodeRange{128336, 128359},
    CodeRange{128378, 128378},
    CodeRange{128405, 128406},
    CodeRange{128420, 128420},
    CodeRange{128507, 128591},
    CodeRange{128640, 128709},
    CodeRange{128716, 128716},
    CodeRange{128720, 128722},
    CodeRange{128725, 128727},
    CodeRange{128732, 128735},
    CodeRange{128747, 128748},
    CodeRange{128756, 128764},
    CodeRange{128992, 129003},
    CodeRange{129008, 129008},
    CodeRange{129292, 129338},
    CodeRange{129340, 129349},
    CodeRange{129351, 129535},
    CodeRange{129648, 129660},
    CodeRange{129664, 129672},
    CodeRange{129680, 129725},
    CodeRange{129727, 129733},
    CodeRange{129742, 129755},
    CodeRange{129760, 129768},
    CodeRange{129776, 129784},
    CodeRange{131072, 196605},
    CodeRange{196608, 262141},
  ], code)

# Unicode 15.1 nonspacing and enclosing mark ranges (Mn and Me).
# Source: https://www.unicode.org/Public/15.1.0/ucd/UnicodeData.txt
def unicode_is_zero_mark(code: U32) -> Bool:
  contains_range([
    CodeRange{768, 879},
    CodeRange{1155, 1161},
    CodeRange{1425, 1469},
    CodeRange{1471, 1471},
    CodeRange{1473, 1474},
    CodeRange{1476, 1477},
    CodeRange{1479, 1479},
    CodeRange{1552, 1562},
    CodeRange{1611, 1631},
    CodeRange{1648, 1648},
    CodeRange{1750, 1756},
    CodeRange{1759, 1764},
    CodeRange{1767, 1768},
    CodeRange{1770, 1773},
    CodeRange{1809, 1809},
    CodeRange{1840, 1866},
    CodeRange{1958, 1968},
    CodeRange{2027, 2035},
    CodeRange{2045, 2045},
    CodeRange{2070, 2073},
    CodeRange{2075, 2083},
    CodeRange{2085, 2087},
    CodeRange{2089, 2093},
    CodeRange{2137, 2139},
    CodeRange{2200, 2207},
    CodeRange{2250, 2273},
    CodeRange{2275, 2306},
    CodeRange{2362, 2362},
    CodeRange{2364, 2364},
    CodeRange{2369, 2376},
    CodeRange{2381, 2381},
    CodeRange{2385, 2391},
    CodeRange{2402, 2403},
    CodeRange{2433, 2433},
    CodeRange{2492, 2492},
    CodeRange{2497, 2500},
    CodeRange{2509, 2509},
    CodeRange{2530, 2531},
    CodeRange{2558, 2558},
    CodeRange{2561, 2562},
    CodeRange{2620, 2620},
    CodeRange{2625, 2626},
    CodeRange{2631, 2632},
    CodeRange{2635, 2637},
    CodeRange{2641, 2641},
    CodeRange{2672, 2673},
    CodeRange{2677, 2677},
    CodeRange{2689, 2690},
    CodeRange{2748, 2748},
    CodeRange{2753, 2757},
    CodeRange{2759, 2760},
    CodeRange{2765, 2765},
    CodeRange{2786, 2787},
    CodeRange{2810, 2815},
    CodeRange{2817, 2817},
    CodeRange{2876, 2876},
    CodeRange{2879, 2879},
    CodeRange{2881, 2884},
    CodeRange{2893, 2893},
    CodeRange{2901, 2902},
    CodeRange{2914, 2915},
    CodeRange{2946, 2946},
    CodeRange{3008, 3008},
    CodeRange{3021, 3021},
    CodeRange{3072, 3072},
    CodeRange{3076, 3076},
    CodeRange{3132, 3132},
    CodeRange{3134, 3136},
    CodeRange{3142, 3144},
    CodeRange{3146, 3149},
    CodeRange{3157, 3158},
    CodeRange{3170, 3171},
    CodeRange{3201, 3201},
    CodeRange{3260, 3260},
    CodeRange{3263, 3263},
    CodeRange{3270, 3270},
    CodeRange{3276, 3277},
    CodeRange{3298, 3299},
    CodeRange{3328, 3329},
    CodeRange{3387, 3388},
    CodeRange{3393, 3396},
    CodeRange{3405, 3405},
    CodeRange{3426, 3427},
    CodeRange{3457, 3457},
    CodeRange{3530, 3530},
    CodeRange{3538, 3540},
    CodeRange{3542, 3542},
    CodeRange{3633, 3633},
    CodeRange{3636, 3642},
    CodeRange{3655, 3662},
    CodeRange{3761, 3761},
    CodeRange{3764, 3772},
    CodeRange{3784, 3790},
    CodeRange{3864, 3865},
    CodeRange{3893, 3893},
    CodeRange{3895, 3895},
    CodeRange{3897, 3897},
    CodeRange{3953, 3966},
    CodeRange{3968, 3972},
    CodeRange{3974, 3975},
    CodeRange{3981, 3991},
    CodeRange{3993, 4028},
    CodeRange{4038, 4038},
    CodeRange{4141, 4144},
    CodeRange{4146, 4151},
    CodeRange{4153, 4154},
    CodeRange{4157, 4158},
    CodeRange{4184, 4185},
    CodeRange{4190, 4192},
    CodeRange{4209, 4212},
    CodeRange{4226, 4226},
    CodeRange{4229, 4230},
    CodeRange{4237, 4237},
    CodeRange{4253, 4253},
    CodeRange{4957, 4959},
    CodeRange{5906, 5908},
    CodeRange{5938, 5939},
    CodeRange{5970, 5971},
    CodeRange{6002, 6003},
    CodeRange{6068, 6069},
    CodeRange{6071, 6077},
    CodeRange{6086, 6086},
    CodeRange{6089, 6099},
    CodeRange{6109, 6109},
    CodeRange{6155, 6157},
    CodeRange{6159, 6159},
    CodeRange{6277, 6278},
    CodeRange{6313, 6313},
    CodeRange{6432, 6434},
    CodeRange{6439, 6440},
    CodeRange{6450, 6450},
    CodeRange{6457, 6459},
    CodeRange{6679, 6680},
    CodeRange{6683, 6683},
    CodeRange{6742, 6742},
    CodeRange{6744, 6750},
    CodeRange{6752, 6752},
    CodeRange{6754, 6754},
    CodeRange{6757, 6764},
    CodeRange{6771, 6780},
    CodeRange{6783, 6783},
    CodeRange{6832, 6862},
    CodeRange{6912, 6915},
    CodeRange{6964, 6964},
    CodeRange{6966, 6970},
    CodeRange{6972, 6972},
    CodeRange{6978, 6978},
    CodeRange{7019, 7027},
    CodeRange{7040, 7041},
    CodeRange{7074, 7077},
    CodeRange{7080, 7081},
    CodeRange{7083, 7085},
    CodeRange{7142, 7142},
    CodeRange{7144, 7145},
    CodeRange{7149, 7149},
    CodeRange{7151, 7153},
    CodeRange{7212, 7219},
    CodeRange{7222, 7223},
    CodeRange{7376, 7378},
    CodeRange{7380, 7392},
    CodeRange{7394, 7400},
    CodeRange{7405, 7405},
    CodeRange{7412, 7412},
    CodeRange{7416, 7417},
    CodeRange{7616, 7679},
    CodeRange{8400, 8432},
    CodeRange{11503, 11505},
    CodeRange{11647, 11647},
    CodeRange{11744, 11775},
    CodeRange{12330, 12333},
    CodeRange{12441, 12442},
    CodeRange{42607, 42610},
    CodeRange{42612, 42621},
    CodeRange{42654, 42655},
    CodeRange{42736, 42737},
    CodeRange{43010, 43010},
    CodeRange{43014, 43014},
    CodeRange{43019, 43019},
    CodeRange{43045, 43046},
    CodeRange{43052, 43052},
    CodeRange{43204, 43205},
    CodeRange{43232, 43249},
    CodeRange{43263, 43263},
    CodeRange{43302, 43309},
    CodeRange{43335, 43345},
    CodeRange{43392, 43394},
    CodeRange{43443, 43443},
    CodeRange{43446, 43449},
    CodeRange{43452, 43453},
    CodeRange{43493, 43493},
    CodeRange{43561, 43566},
    CodeRange{43569, 43570},
    CodeRange{43573, 43574},
    CodeRange{43587, 43587},
    CodeRange{43596, 43596},
    CodeRange{43644, 43644},
    CodeRange{43696, 43696},
    CodeRange{43698, 43700},
    CodeRange{43703, 43704},
    CodeRange{43710, 43711},
    CodeRange{43713, 43713},
    CodeRange{43756, 43757},
    CodeRange{43766, 43766},
    CodeRange{44005, 44005},
    CodeRange{44008, 44008},
    CodeRange{44013, 44013},
    CodeRange{64286, 64286},
    CodeRange{65024, 65039},
    CodeRange{65056, 65071},
    CodeRange{66045, 66045},
    CodeRange{66272, 66272},
    CodeRange{66422, 66426},
    CodeRange{68097, 68099},
    CodeRange{68101, 68102},
    CodeRange{68108, 68111},
    CodeRange{68152, 68154},
    CodeRange{68159, 68159},
    CodeRange{68325, 68326},
    CodeRange{68900, 68903},
    CodeRange{69291, 69292},
    CodeRange{69373, 69375},
    CodeRange{69446, 69456},
    CodeRange{69506, 69509},
    CodeRange{69633, 69633},
    CodeRange{69688, 69702},
    CodeRange{69744, 69744},
    CodeRange{69747, 69748},
    CodeRange{69759, 69761},
    CodeRange{69811, 69814},
    CodeRange{69817, 69818},
    CodeRange{69826, 69826},
    CodeRange{69888, 69890},
    CodeRange{69927, 69931},
    CodeRange{69933, 69940},
    CodeRange{70003, 70003},
    CodeRange{70016, 70017},
    CodeRange{70070, 70078},
    CodeRange{70089, 70092},
    CodeRange{70095, 70095},
    CodeRange{70191, 70193},
    CodeRange{70196, 70196},
    CodeRange{70198, 70199},
    CodeRange{70206, 70206},
    CodeRange{70209, 70209},
    CodeRange{70367, 70367},
    CodeRange{70371, 70378},
    CodeRange{70400, 70401},
    CodeRange{70459, 70460},
    CodeRange{70464, 70464},
    CodeRange{70502, 70508},
    CodeRange{70512, 70516},
    CodeRange{70712, 70719},
    CodeRange{70722, 70724},
    CodeRange{70726, 70726},
    CodeRange{70750, 70750},
    CodeRange{70835, 70840},
    CodeRange{70842, 70842},
    CodeRange{70847, 70848},
    CodeRange{70850, 70851},
    CodeRange{71090, 71093},
    CodeRange{71100, 71101},
    CodeRange{71103, 71104},
    CodeRange{71132, 71133},
    CodeRange{71219, 71226},
    CodeRange{71229, 71229},
    CodeRange{71231, 71232},
    CodeRange{71339, 71339},
    CodeRange{71341, 71341},
    CodeRange{71344, 71349},
    CodeRange{71351, 71351},
    CodeRange{71453, 71455},
    CodeRange{71458, 71461},
    CodeRange{71463, 71467},
    CodeRange{71727, 71735},
    CodeRange{71737, 71738},
    CodeRange{71995, 71996},
    CodeRange{71998, 71998},
    CodeRange{72003, 72003},
    CodeRange{72148, 72151},
    CodeRange{72154, 72155},
    CodeRange{72160, 72160},
    CodeRange{72193, 72202},
    CodeRange{72243, 72248},
    CodeRange{72251, 72254},
    CodeRange{72263, 72263},
    CodeRange{72273, 72278},
    CodeRange{72281, 72283},
    CodeRange{72330, 72342},
    CodeRange{72344, 72345},
    CodeRange{72752, 72758},
    CodeRange{72760, 72765},
    CodeRange{72767, 72767},
    CodeRange{72850, 72871},
    CodeRange{72874, 72880},
    CodeRange{72882, 72883},
    CodeRange{72885, 72886},
    CodeRange{73009, 73014},
    CodeRange{73018, 73018},
    CodeRange{73020, 73021},
    CodeRange{73023, 73029},
    CodeRange{73031, 73031},
    CodeRange{73104, 73105},
    CodeRange{73109, 73109},
    CodeRange{73111, 73111},
    CodeRange{73459, 73460},
    CodeRange{73472, 73473},
    CodeRange{73526, 73530},
    CodeRange{73536, 73536},
    CodeRange{73538, 73538},
    CodeRange{78912, 78912},
    CodeRange{78919, 78933},
    CodeRange{92912, 92916},
    CodeRange{92976, 92982},
    CodeRange{94031, 94031},
    CodeRange{94095, 94098},
    CodeRange{94180, 94180},
    CodeRange{113821, 113822},
    CodeRange{118528, 118573},
    CodeRange{118576, 118598},
    CodeRange{119143, 119145},
    CodeRange{119163, 119170},
    CodeRange{119173, 119179},
    CodeRange{119210, 119213},
    CodeRange{119362, 119364},
    CodeRange{121344, 121398},
    CodeRange{121403, 121452},
    CodeRange{121461, 121461},
    CodeRange{121476, 121476},
    CodeRange{121499, 121503},
    CodeRange{121505, 121519},
    CodeRange{122880, 122886},
    CodeRange{122888, 122904},
    CodeRange{122907, 122913},
    CodeRange{122915, 122916},
    CodeRange{122918, 122922},
    CodeRange{123023, 123023},
    CodeRange{123184, 123190},
    CodeRange{123566, 123566},
    CodeRange{123628, 123631},
    CodeRange{124140, 124143},
    CodeRange{125136, 125142},
    CodeRange{125252, 125258},
    CodeRange{917760, 917999},
  ], code)

def is_zero_code(+code: U32) -> Bool:
  Bool.or(U32.is_le(code, 31), Bool.or(
    Bool.and(U32.is_ge(code, 127), U32.is_le(code, 159)), Bool.or(
    unicode_is_zero_mark(code), Bool.or(
    Bool.and(U32.is_ge(code, 8203), U32.is_le(code, 8207)), Bool.or(
    Bool.and(U32.is_ge(code, 65024), U32.is_le(code, 65039)),
    Bool.and(U32.is_ge(code, 917760), U32.is_le(code, 917999)))))))

def code_width(+code: U32) -> Nat:
  Bool.pick(Nat, is_zero_code(code), 0n,
    Bool.pick(Nat, unicode_is_wide(code), 2n, 1n))

def width(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{head, tail}:
      Nat.add(code_width(Char.to_u32(head)), width(tail))

def leading_indent(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+head, tail}:
      Bool.pick(String, Char.is_eq(head, ' '),
        SCon{head, leading_indent(tail)}, "")

type WrapState is Data:
  WrapState{indent: String, cols: Nat, line: String,
    started: Bool, done: List<&2, String>}

def wrap_words(words: List<&2, String>, state: WrapState) -> String:
  match words state:
    case Nil{} WrapState{indent, cols, line, started, done}:
      Bool.pick(String, started,
        String.join(List.reverse(&2, String, line <> done), "\n"), "")
    case +word <> rest WrapState{+indent, +cols, +line, +started, +done}:
      +candidate = Bool.pick(String, started,
        String.append(line, String.append(" ", word)),
        String.append(indent, word))
      fits = Bool.or(Bool.not(started), Nat.is_le(width(strip(candidate)), cols))
      next = Bool.pick(WrapState, fits,
        WrapState{indent, cols, candidate, True{}, done},
        WrapState{indent, cols, String.append(indent, word), True{}, line <> done})
      wrap_words(rest, next)

def wrap_line(+line: String, cols: Nat) -> String:
  +indent = leading_indent(line)
  body = String.drop(line, String.length(indent))
  words = List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
    String.split(body, ' '))
  wrap_words(words, WrapState{indent, cols, indent, False{}, Nil{}})

def wrap_lines(lines: List<&2, String>, +cols: Nat) -> List<&2, String>:
  match lines:
    case Nil{}:
      Nil{}
    case head <> tail:
      wrap_line(head, cols) <> wrap_lines(tail, cols)

def wrap(text: String, cols: Nat) -> String:
  String.join(wrap_lines(String.lines(text), cols), "\n")

type Item is Data:
  Arg{usage: String, help: String, items: List<&2, Item>}
  Sub{name: String, about: String, items: List<&2, Item>}
  Version{value: String}
  Alias{name: String}
  Hidden{}
  Example{line: String, what: String}
  After{text: String}
  SubOptional{}
  External{}
  Exclusive{group: String}
  NeedOne{group: String}
  Id{value: String}
  Required{}
  Default{value: String}
  Env{name: String}
  Global{}
  Heading{title: String}
  AsNat{}
  AsU32{}
  AsF32{}
  AsBool{}
  AsFile{}
  AsDir{}
  OneOf{values: List<&2, String>}
  Delim{sep: Char}
  Hyphen{}
  Rest{}
  Bare{value: String}
  Conflicts{id: String}
  Requires{id: String}
  Group{name: String}

type Cmd is Data:
  Cmd{name: String, about: String, items: List<&2, Item>}

type Problem is Data:
  BadUsage{at: String, usage: String, col: Nat}
  BadName{at: String, name: String}
  Dup{at: String, name: String}
  Reserved{at: String, name: String}
  Misplaced{at: String, attr: String}
  NoHelp{at: String, what: String}
  BadDefault{at: String, id: String, value: String}
  BadRef{at: String, id: String}
  BadPositional{at: String, id: String, why: String}
  Mixed{at: String}
  BadChoices{at: String, id: String}
  NeedBare{at: String, id: String}
  DecodeBug{at: String, msg: String}

def cmd(name: String, about: String, items: List<&2, Item>) -> Cmd:
  Cmd{name, about, items}

def sub(name: String, about: String, items: List<&2, Item>) -> Item:
  Sub{name, about, items}

def arg(usage: String, help: String, items: List<&2, Item>) -> Item:
  Arg{usage, help, items}

def version(value: String) -> Item:
  Version{value}

def alias(name: String) -> Item:
  Alias{name}

def hidden() -> Item:
  Hidden{}

def example(line: String, what: String) -> Item:
  Example{line, what}

def after(text: String) -> Item:
  After{text}

def sub_optional() -> Item:
  SubOptional{}

def external() -> Item:
  External{}

def exclusive(group: String) -> Item:
  Exclusive{group}

def need_one(group: String) -> Item:
  NeedOne{group}

def id(value: String) -> Item:
  Id{value}

def required() -> Item:
  Required{}

def default(value: String) -> Item:
  Default{value}

def env(name: String) -> Item:
  Env{name}

def global() -> Item:
  Global{}

def heading(title: String) -> Item:
  Heading{title}

def as_nat() -> Item:
  AsNat{}

def as_u32() -> Item:
  AsU32{}

def as_f32() -> Item:
  AsF32{}

def as_bool() -> Item:
  AsBool{}

def as_file() -> Item:
  AsFile{}

def as_dir() -> Item:
  AsDir{}

def one_of(values: List<&2, String>) -> Item:
  OneOf{values}

def delim(sep: Char) -> Item:
  Delim{sep}

def hyphen() -> Item:
  Hyphen{}

def rest() -> Item:
  Rest{}

def bare(value: String) -> Item:
  Bare{value}

def conflicts(target: String) -> Item:
  Conflicts{target}

def requires(target: String) -> Item:
  Requires{target}

def group(name: String) -> Item:
  Group{name}

def color() -> Item:
  arg("--color <WHEN>", "When to use color", [one_of(["auto", "always", "never"]), default("auto"), global()])

def completions() -> Item:
  sub("completions", "Print a shell completion script", [arg("<SHELL>", "Shell to generate for", [one_of(["bash", "zsh", "fish"])])])

def man() -> Item:
  sub("man", "Print the man page", [hidden(), arg("[COMMAND]...", "Subcommand path", [])])

type UsageKind is Data:
  FlagKind{}
  CountKind{}
  NegatableKind{}
  OptionKind{}
  ListOptionKind{}
  BareOptionKind{}
  RequiredPosKind{}
  OptionalPosKind{}
  RequiredManyKind{}
  OptionalManyKind{}

type Usage is Data:
  Parsed{id: String, short: String, long: String, kind: UsageKind}
  Invalid{col: Nat}

type NameScan is Data:
  NameOK{name: String, rest: String, next: Nat}
  NameBad{col: Nat}

type PhScan is Data:
  PhOK{name: String, rest: String, next: Nat}
  PhBad{col: Nat}

def name_start(+c: Char) -> Bool:
  Bool.or(Char.is_alpha(c), Char.is_digit(c))

def name_char(+c: Char) -> Bool:
  Bool.or(name_start(c), Bool.or(Char.is_eq(c, '-'),
    Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '.'))))

def finish_name(name: String, rest: String, +pos: Nat,
    +first: Bool, +dot_start: Nat) -> NameScan:
  Bool.pick(NameScan, Bool.or(first, Nat.is_lt(dot_start, pos)),
    NameBad{Bool.pick(Nat, first, pos, dot_start)},
    NameOK{name, rest, pos})

def scan_name(s: String, +pos: Nat, name: String,
    +first: Bool, dot_start: Nat) -> NameScan:
  match s:
    case SNil{}:
      finish_name(name, SNil{}, pos, first, dot_start)
    case SCon{Chr{32}, tail}:
      finish_name(name, SCon{Char.from_u32(32), tail}, pos, first, dot_start)
    case SCon{Chr{91}, tail}:
      finish_name(name, SCon{Char.from_u32(91), tail}, pos, first, dot_start)
    case SCon{+h, tail}:
      valid = Bool.pick(Bool, first, name_start(h), name_char(h))
      next_dot = Bool.pick(Nat, Char.is_eq(h, '.'), dot_start, Nat.add(pos, 1n))
      Bool.pick(NameScan, valid,
        scan_name(tail, Nat.add(pos, 1n), String.append(name, Char.show(h)),
          False{}, next_dot),
        NameBad{pos})

def ph_char(+c: Char) -> Bool:
  Bool.not(Bool.or(Char.is_eq(c, ' '), Bool.or(Char.is_eq(c, '<'),
    Bool.or(Char.is_eq(c, '>'), Bool.or(Char.is_eq(c, '['),
    Bool.or(Char.is_eq(c, ']'), Char.is_eq(c, '=')))))))

def scan_ph(s: String, +pos: Nat, +name: String, +close: Char) -> PhScan:
  match s:
    case SNil{}:
      PhBad{pos}
    case SCon{+h, +tail}:
      Bool.pick(PhScan, Char.is_eq(h, close),
        Bool.pick(PhScan, String.is_empty(name), PhBad{pos},
          PhOK{name, tail, Nat.add(pos, 1n)}),
        Bool.pick(PhScan, ph_char(h),
          scan_ph(tail, Nat.add(pos, 1n), String.append(name, Char.show(h)), close),
          PhBad{pos}))

def finish_pos(found: PhScan, kind: UsageKind) -> Usage:
  match found:
    case PhBad{col}:
      Invalid{col}
    case PhOK{name, SNil{}, next}:
      Parsed{String.to_lower(name), "", "", kind}
    case PhOK{name, rest, next}:
      Invalid{next}

def parse_pos(s: String, +repeat: Bool) -> Usage:
  match s:
    case SCon{Chr{60}, tail}:
      finish_pos(scan_ph(tail, 1n, "", '>'),
        Bool.pick(UsageKind, repeat, RequiredManyKind{}, RequiredPosKind{}))
    case SCon{Chr{91}, tail}:
      finish_pos(scan_ph(tail, 1n, "", ']'),
        Bool.pick(UsageKind, repeat, OptionalManyKind{}, OptionalPosKind{}))
    case _:
      Invalid{0n}

def finish_required_value(found: PhScan, id: String, short: String,
    long: String, kind: UsageKind) -> Usage:
  match found:
    case PhBad{col}:
      Invalid{col}
    case PhOK{name, SNil{}, next}:
      Parsed{id, short, long, kind}
    case PhOK{name, rest, next}:
      Invalid{next}

def finish_optional_value(found: PhScan, id: String, short: String,
    long: String) -> Usage:
  match found:
    case PhBad{col}:
      Invalid{col}
    case PhOK{name, SCon{Chr{93}, SNil{}}, next}:
      Parsed{id, short, long, BareOptionKind{}}
    case PhOK{name, rest, next}:
      Invalid{next}

def finish_long(found: NameScan, short: String,
    +repeat: Bool, +negatable: Bool) -> Usage:
  match found:
    case NameBad{col}:
      Invalid{col}
    case NameOK{+name, SNil{}, next}:
      Parsed{name, short, String.append("--", name),
        Bool.pick(UsageKind, negatable, NegatableKind{},
          Bool.pick(UsageKind, repeat, CountKind{}, FlagKind{}))}
    case NameOK{+name, SCon{Chr{32}, SCon{Chr{60}, tail}}, +next}:
      Bool.pick(Usage, negatable, Invalid{next},
        finish_required_value(scan_ph(tail, Nat.add(next, 2n), "", '>'),
          name, short, String.append("--", name),
          Bool.pick(UsageKind, repeat, ListOptionKind{}, OptionKind{})))
    case NameOK{+name, SCon{Chr{91}, SCon{Chr{61}, SCon{Chr{60}, tail}}}, +next}:
      Bool.pick(Usage, Bool.or(negatable, repeat), Invalid{next},
        finish_optional_value(scan_ph(tail, Nat.add(next, 3n), "", '>'),
          name, short, String.append("--", name)))
    case NameOK{name, rest, next}:
      Invalid{next}

def parse_long_prefixed(+s: String, +short: String,
    +repeat: Bool, +start: Nat) -> Usage:
  Bool.pick(Usage, String.starts_with(s, "--[no-]"),
    finish_long(scan_name(String.drop(s, 7n), Nat.add(start, 7n),
      "", True{}, Nat.add(start, 7n)), short, repeat, True{}),
    Bool.pick(Usage, String.starts_with(s, "--"),
      finish_long(scan_name(String.drop(s, 2n), Nat.add(start, 2n),
        "", True{}, Nat.add(start, 2n)), short, repeat, False{}),
      Invalid{start}))

def parse_short_tail(tail: String, +short: String, +repeat: Bool) -> Usage:
  match tail:
    case SNil{}:
      Parsed{String.drop(short, 1n), short, "",
        Bool.pick(UsageKind, repeat, CountKind{}, FlagKind{})}
    case SCon{Chr{44}, SCon{Chr{32}, long_rest}}:
      parse_long_prefixed(long_rest, short, repeat, 4n)
    case SCon{Chr{32}, SCon{Chr{60}, ph_rest}}:
      finish_required_value(scan_ph(ph_rest, 4n, "", '>'),
        String.drop(short, 1n), short, "",
        Bool.pick(UsageKind, repeat, ListOptionKind{}, OptionKind{}))
    case SCon{Chr{91}, SCon{Chr{61}, SCon{Chr{60}, ph_rest}}}:
      finish_optional_value(scan_ph(ph_rest, 5n, "", '>'),
        String.drop(short, 1n), short, "")
    case _:
      Invalid{2n}

def parse_short(s: String, repeat: Bool) -> Usage:
  match s:
    case SCon{Chr{45}, SCon{+h, tail}}:
      Bool.pick(Usage, name_start(h),
        parse_short_tail(tail, String.append("-", Char.show(h)), repeat),
        Invalid{1n})
    case _:
      Invalid{1n}

def parse_usage_body(s: String, +repeat: Bool) -> Usage:
  match s:
    case SCon{Chr{60}, tail}:
      parse_pos(SCon{Char.from_u32(60), tail}, repeat)
    case SCon{Chr{91}, tail}:
      parse_pos(SCon{Char.from_u32(91), tail}, repeat)
    case SCon{Chr{45}, SCon{Chr{45}, tail}}:
      parse_long_prefixed(String.append("--", tail), "", repeat, 0n)
    case SCon{Chr{45}, tail}:
      parse_short(SCon{Char.from_u32(45), tail}, repeat)
    case _:
      Invalid{0n}

def parse_usage(+usage: String) -> Usage:
  +repeated = String.ends_with(usage, "...")
  body = Bool.pick(String, repeated,
    String.take(usage, Nat.sub(String.length(usage), 3n)), usage)
  parse_usage_body(body, repeated)

def alias_valid_result(parsed: Usage, +raw: String) -> Bool:
  match parsed:
    case Parsed{id, short, long, FlagKind{}}:
      Bool.or(String.eq(raw, short), String.eq(raw, long))
    case _: False{}

def valid_arg_alias(+raw: String) -> Bool:
  alias_valid_result(parse_usage(raw), raw)

def kind_pos(kind: UsageKind) -> Bool:
  match kind:
    case RequiredPosKind{}: True{}
    case OptionalPosKind{}: True{}
    case RequiredManyKind{}: True{}
    case OptionalManyKind{}: True{}
    case _: False{}

def kind_optional_pos(kind: UsageKind) -> Bool:
  match kind:
    case OptionalPosKind{}: True{}
    case OptionalManyKind{}: True{}
    case _: False{}

def kind_variadic_pos(kind: UsageKind) -> Bool:
  match kind:
    case RequiredManyKind{}: True{}
    case OptionalManyKind{}: True{}
    case _: False{}

def kind_required_pos(kind: UsageKind) -> Bool:
  match kind:
    case RequiredPosKind{}: True{}
    case RequiredManyKind{}: True{}
    case _: False{}

def kind_valued(kind: UsageKind) -> Bool:
  match kind:
    case OptionKind{}: True{}
    case ListOptionKind{}: True{}
    case BareOptionKind{}: True{}
    case RequiredPosKind{}: True{}
    case OptionalPosKind{}: True{}
    case RequiredManyKind{}: True{}
    case OptionalManyKind{}: True{}
    case _: False{}

def kind_bare(kind: UsageKind) -> Bool:
  match kind:
    case BareOptionKind{}: True{}
    case _: False{}

def kind_default_allowed(kind: UsageKind) -> Bool:
  match kind:
    case OptionKind{}: True{}
    case ListOptionKind{}: True{}
    case BareOptionKind{}: True{}
    case OptionalPosKind{}: True{}
    case OptionalManyKind{}: True{}
    case NegatableKind{}: True{}
    case _: False{}

def kind_required_allowed(kind: UsageKind) -> Bool:
  match kind:
    case OptionKind{}: True{}
    case ListOptionKind{}: True{}
    case _: False{}

def kind_delim_allowed(kind: UsageKind) -> Bool:
  match kind:
    case ListOptionKind{}: True{}
    case RequiredManyKind{}: True{}
    case OptionalManyKind{}: True{}
    case _: False{}

def bad_attr(cond: Bool, name: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, cond, Some{name}, None{})

def misplaced_attr_name(attr: Item, +kind: UsageKind) ->
    Maybe<&2, String>:
  match attr:
    case Global{}: bad_attr(kind_pos(kind), "global")
    case Rest{}: bad_attr(Bool.not(kind_variadic_pos(kind)), "rest")
    case Default{value}:
      bad_attr(Bool.not(kind_default_allowed(kind)), "default")
    case Required{}:
      bad_attr(Bool.not(kind_required_allowed(kind)), "required")
    case Heading{title}: bad_attr(kind_pos(kind), "heading")
    case Alias{name}: bad_attr(kind_pos(kind), "alias")
    case AsNat{}: bad_attr(Bool.not(kind_valued(kind)), "as_nat")
    case AsU32{}: bad_attr(Bool.not(kind_valued(kind)), "as_u32")
    case AsF32{}: bad_attr(Bool.not(kind_valued(kind)), "as_f32")
    case AsBool{}: bad_attr(Bool.not(kind_valued(kind)), "as_bool")
    case AsFile{}: bad_attr(Bool.not(kind_valued(kind)), "as_file")
    case AsDir{}: bad_attr(Bool.not(kind_valued(kind)), "as_dir")
    case OneOf{values}:
      bad_attr(Bool.not(kind_valued(kind)), "one_of")
    case Delim{sep}: bad_attr(Bool.not(kind_delim_allowed(kind)), "delim")
    case Hyphen{}: bad_attr(Bool.not(kind_valued(kind)), "hyphen")
    case Arg{usage, help, items}: Some{"arg"}
    case Sub{name, about, items}: Some{"sub"}
    case Version{value}: Some{"version"}
    case Example{line, what}: Some{"example"}
    case After{text}: Some{"after"}
    case SubOptional{}: Some{"sub_optional"}
    case External{}: Some{"external"}
    case Exclusive{group}: Some{"exclusive"}
    case NeedOne{group}: Some{"need_one"}
    case _: None{}

def maybe_misplaced(found: Maybe<&2, String>, at: String) ->
    List<&2, Problem>:
  match found:
    case None{}: Nil{}
    case Some{name}: [Misplaced{at, name}]

def placement_issues(attrs: List<&2, Item>, +kind: UsageKind,
    +at: String) -> List<&2, Problem>:
  match attrs:
    case Nil{}: Nil{}
    case head <> tail:
      List.append(&2, Problem,
        maybe_misplaced(misplaced_attr_name(head, kind), at),
        placement_issues(tail, kind, at))

def value_type_names(attrs: List<&2, Item>) -> List<&2, String>:
  match attrs:
    case Nil{}: Nil{}
    case AsNat{} <> tail: "as_nat" <> value_type_names(tail)
    case AsU32{} <> tail: "as_u32" <> value_type_names(tail)
    case AsF32{} <> tail: "as_f32" <> value_type_names(tail)
    case AsBool{} <> tail: "as_bool" <> value_type_names(tail)
    case AsFile{} <> tail: "as_file" <> value_type_names(tail)
    case AsDir{} <> tail: "as_dir" <> value_type_names(tail)
    case head <> tail: value_type_names(tail)

def extra_type_issues(names: List<&2, String>, +at: String) ->
    List<&2, Problem>:
  match names:
    case Nil{}: Nil{}
    case name <> tail:
      Misplaced{at, name} <> extra_type_issues(tail, at)

def duplicate_type_issues(names: List<&2, String>, at: String) ->
    List<&2, Problem>:
  match names:
    case Nil{}: Nil{}
    case head <> tail: extra_type_issues(tail, at)

def command_attr_name(attr: Item, root: Bool) -> Maybe<&2, String>:
  match attr:
    case Arg{usage, help, attrs}: None{}
    case Sub{name, about, children}: None{}
    case Version{value}: bad_attr(Bool.not(root), "version")
    case Alias{name}: bad_attr(root, "alias")
    case Hidden{}: bad_attr(root, "hidden")
    case Example{line, what}: None{}
    case After{text}: None{}
    case SubOptional{}: None{}
    case External{}: None{}
    case Exclusive{group}: None{}
    case NeedOne{group}: None{}
    case Id{value}: Some{"id"}
    case Required{}: Some{"required"}
    case Default{value}: Some{"default"}
    case Env{name}: Some{"env"}
    case Global{}: Some{"global"}
    case Heading{title}: Some{"heading"}
    case AsNat{}: Some{"as_nat"}
    case AsU32{}: Some{"as_u32"}
    case AsF32{}: Some{"as_f32"}
    case AsBool{}: Some{"as_bool"}
    case AsFile{}: Some{"as_file"}
    case AsDir{}: Some{"as_dir"}
    case OneOf{values}: Some{"one_of"}
    case Delim{sep}: Some{"delim"}
    case Hyphen{}: Some{"hyphen"}
    case Rest{}: Some{"rest"}
    case Bare{value}: Some{"bare"}
    case Conflicts{id}: Some{"conflicts"}
    case Requires{id}: Some{"requires"}
    case Group{name}: Some{"group"}

def has_rest(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Rest{} <> tail: True{}
    case head <> tail: has_rest(tail)

def has_hidden(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Hidden{} <> tail: True{}
    case head <> tail: has_hidden(tail)

def has_bare(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Bare{value} <> tail: True{}
    case head <> tail: has_bare(tail)

def has_as_u32(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case AsU32{} <> tail: True{}
    case head <> tail: has_as_u32(tail)

def has_required(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Required{} <> tail: True{}
    case head <> tail: has_required(tail)

def duplicate_strings(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: False{}
    case +head <> +tail:
      Bool.or(List.contains(~String, ~String.eq, tail, head),
        duplicate_strings(tail))

def bad_choices(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case OneOf{+values} <> tail:
      Bool.or(Bool.or(List.is_empty(&2, String, values),
        duplicate_strings(values)), bad_choices(tail))
    case head <> tail: bad_choices(tail)

def find_default(items: List<&2, Item>) -> Maybe<&2, String>:
  match items:
    case Nil{}: None{}
    case Default{value} <> tail: Some{value}
    case head <> tail: find_default(tail)

def find_id(items: List<&2, Item>) -> Maybe<&2, String>:
  match items:
    case Nil{}: None{}
    case Id{value} <> tail: Some{value}
    case head <> tail: find_id(tail)

def find_requires(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Requires{target} <> tail: target <> find_requires(tail)
    case head <> tail: find_requires(tail)

def find_conflicts(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Conflicts{target} <> tail: target <> find_conflicts(tail)
    case head <> tail: find_conflicts(tail)

def find_group_attrs(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Group{name} <> tail: name <> find_group_attrs(tail)
    case head <> tail: find_group_attrs(tail)

def find_aliases(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Alias{name} <> tail: name <> find_aliases(tail)
    case head <> tail: find_aliases(tail)

def scope_groups(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Arg{usage, help, attrs} <> tail:
      List.append(&2, String, find_group_attrs(attrs), scope_groups(tail))
    case head <> tail: scope_groups(tail)

def scope_group_rules(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Exclusive{group} <> tail: group <> scope_group_rules(tail)
    case NeedOne{group} <> tail: group <> scope_group_rules(tail)
    case head <> tail: scope_group_rules(tail)

def parsed_is_pos(usage: Usage) -> Bool:
  match usage:
    case Parsed{id, short, long, kind}: kind_pos(kind)
    case Invalid{col}: False{}

def has_pos_item(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Arg{usage, help, attrs} <> tail:
      Bool.or(parsed_is_pos(parse_usage(usage)), has_pos_item(tail))
    case head <> tail: has_pos_item(tail)

def has_sub_item(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Sub{name, about, children} <> tail: True{}
    case head <> tail: has_sub_item(tail)

def has_version_item(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Version{value} <> tail: True{}
    case head <> tail: has_version_item(tail)

def name_scan_valid(result: NameScan) -> Bool:
  match result:
    case NameOK{name, SNil{}, next}: True{}
    case _: False{}

def valid_command_name(s: String) -> Bool:
  name_scan_valid(scan_name(s, 0n, "", True{}, 0n))

def use_id(found: Maybe<&2, String>, derived: String) -> String:
  match found:
    case None{}: derived
    case Some{explicit}: explicit

def usage_id(parsed: Usage, attrs: List<&2, Item>) -> String:
  match parsed:
    case Parsed{derived, short, long, kind}:
      use_id(find_id(attrs), derived)
    case Invalid{col}:
      ""

def scope_ids(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case Arg{usage, help, attrs} <> tail:
      +name = usage_id(parse_usage(usage), attrs)
      +rest = scope_ids(tail)
      Bool.pick(List<&2, String>, String.is_empty(name),
        rest, name <> rest)
    case head <> tail:
      scope_ids(tail)

type Seen is Data:
  SeenArg{id: String, short: String, long: String}
  SeenSub{name: String}
  SeenArgAlias{name: String}
  SeenSubAlias{name: String}

def same_nonempty(+a: String, b: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(a)), String.eq(a, b))

def arg_collision(seen: List<&2, Seen>, +id: String,
    +short: String, +long: String) -> Maybe<&2, String>:
  match seen:
    case Nil{}:
      None{}
    case SeenArg{old_id, old_short, old_long} <> tail:
      here = Bool.pick(Maybe<&2, String>, same_nonempty(short, old_short),
        Some{short}, Bool.pick(Maybe<&2, String>,
          same_nonempty(long, old_long), Some{long},
          Bool.pick(Maybe<&2, String>, String.eq(id, old_id), Some{id}, None{})))
      Maybe.or(&2, String, here, arg_collision(tail, id, short, long))
    case SeenArgAlias{+old} <> tail:
      Bool.pick(Maybe<&2, String>, same_nonempty(short, old),
        Some{short}, Bool.pick(Maybe<&2, String>,
          same_nonempty(long, old), Some{long},
          arg_collision(tail, id, short, long)))
    case head <> tail:
      arg_collision(tail, id, short, long)

def sub_collision(seen: List<&2, Seen>, +name: String) -> Bool:
  match seen:
    case Nil{}:
      False{}
    case SeenSub{old} <> tail:
      Bool.or(String.eq(name, old), sub_collision(tail, name))
    case SeenSubAlias{old} <> tail:
      Bool.or(String.eq(name, old), sub_collision(tail, name))
    case head <> tail:
      sub_collision(tail, name)

def arg_alias_collision(seen: List<&2, Seen>, +name: String) -> Bool:
  match seen:
    case Nil{}: False{}
    case SeenArg{id, short, long} <> tail:
      Bool.or(Bool.or(same_nonempty(name, short),
        same_nonempty(name, long)), arg_alias_collision(tail, name))
    case SeenArgAlias{old} <> tail:
      Bool.or(String.eq(name, old), arg_alias_collision(tail, name))
    case head <> tail:
      arg_alias_collision(tail, name)

def maybe_dup(found: Maybe<&2, String>, at: String) -> List<&2, Problem>:
  match found:
    case None{}: Nil{}
    case Some{name}: [Dup{at, name}]

def when_problem(cond: Bool, problem: Problem) -> List<&2, Problem>:
  Bool.pick(List<&2, Problem>, cond, [problem], Nil{})

def arg_alias_issue(+name: String, +at: String,
    seen: List<&2, Seen>, version: Bool) -> List<&2, Problem>:
  Bool.pick(List<&2, Problem>, valid_arg_alias(name),
    Bool.pick(List<&2, Problem>, Bool.or(String.eq(name, "--help"),
      Bool.and(version, String.eq(name, "--version"))),
      [Reserved{at, name}],
      when_problem(arg_alias_collision(seen, name), Dup{at, name})),
    [BadName{at, name}])

def arg_alias_issues(aliases: List<&2, String>, +at: String,
    +seen: List<&2, Seen>, +version: Bool) -> List<&2, Problem>:
  match aliases:
    case Nil{}: Nil{}
    case +name <> tail:
      List.append(&2, Problem,
        arg_alias_issue(name, at, seen, version),
        arg_alias_issues(tail, at, SeenArgAlias{name} <> seen, version))

def arg_alias_entries(aliases: List<&2, String>) -> List<&2, Seen>:
  match aliases:
    case Nil{}: Nil{}
    case name <> tail:
      SeenArgAlias{name} <> arg_alias_entries(tail)

def sub_alias_issue(+name: String, +at: String,
    seen: List<&2, Seen>) -> List<&2, Problem>:
  Bool.pick(List<&2, Problem>, valid_command_name(name),
    Bool.pick(List<&2, Problem>, String.eq(name, "help"),
      [Reserved{at, name}],
      when_problem(sub_collision(seen, name), Dup{at, name})),
    [BadName{at, name}])

def sub_alias_issues(aliases: List<&2, String>, +at: String,
    +seen: List<&2, Seen>) -> List<&2, Problem>:
  match aliases:
    case Nil{}: Nil{}
    case +name <> tail:
      List.append(&2, Problem,
        sub_alias_issue(name, at, seen),
        sub_alias_issues(tail, at, SeenSubAlias{name} <> seen))

def sub_alias_entries(aliases: List<&2, String>) -> List<&2, Seen>:
  match aliases:
    case Nil{}: Nil{}
    case name <> tail:
      SeenSubAlias{name} <> sub_alias_entries(tail)

def missing_refs(targets: List<&2, String>, +ids: List<&2, String>,
    +at: String) -> List<&2, Problem>:
  match targets:
    case Nil{}:
      Nil{}
    case +target <> tail:
      List.append(&2, Problem,
        when_problem(Bool.not(List.contains(~String, ~String.eq, ids, target)),
          BadRef{at, target}), missing_refs(tail, ids, at))

def u32_digits(s: String, +acc: U32) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, tail}:
      +digit = U32.sub(Char.to_u32(h), 48)
      valid = Bool.and(Char.is_digit(h),
        Bool.or(U32.is_lt(acc, 429496729),
          Bool.and(U32.is_eq(acc, 429496729), U32.is_le(digit, 5))))
      Bool.pick(Bool, valid,
        u32_digits(tail, U32.add(U32.mul(acc, 10), digit)), False{})

def valid_u32(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), u32_digits(s, 0))

def decimal_digits(s: String) -> Bool:
  match s:
    case SNil{}: True{}
    case SCon{head, tail}:
      Bool.and(Char.is_digit(head), decimal_digits(tail))

def trim_zeroes(s: String) -> String:
  match s:
    case SCon{Chr{48}, tail}: trim_zeroes(tail)
    case SNil{}: SNil{}
    case SCon{head, tail}: SCon{head, tail}

def nat_fits(+digits: String) -> Bool:
  +length = String.length(digits)
  Bool.or(Nat.is_lt(length, 15n),
    Bool.and(Nat.is_eq(length, 15n),
      String.is_le(digits, "281474976710655")))

def valid_nat(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)),
    Bool.and(decimal_digits(s), nat_fits(trim_zeroes(s))))

def valid_bool(s: String) -> Bool:
  List.contains(~String, ~String.eq,
    ["true", "false", "yes", "no", "on", "off", "1", "0"],
    String.to_lower(s))

type DecimalState is Data:
  DecStart{}
  DecAfterMinus{}
  DecInt{}
  DecDotFirst{}
  DecDotAfterInt{}
  DecFrac{}
  DecExpStart{}
  DecExpSign{}
  DecExpDigits{}
  DecInvalid{}

def is_exponent(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, 'e'), Char.is_eq(c, 'E'))

def is_sign(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, '+'), Char.is_eq(c, '-'))

def decimal_step(state: DecimalState, +c: Char) -> DecimalState:
  match state:
    case DecStart{}:
      Bool.pick(DecimalState, Char.is_eq(c, '-'), DecAfterMinus{},
        Bool.pick(DecimalState, Char.is_digit(c), DecInt{},
          Bool.pick(DecimalState, Char.is_eq(c, '.'), DecDotFirst{}, DecInvalid{})))
    case DecAfterMinus{}:
      Bool.pick(DecimalState, Char.is_digit(c), DecInt{},
        Bool.pick(DecimalState, Char.is_eq(c, '.'), DecDotFirst{}, DecInvalid{}))
    case DecInt{}:
      Bool.pick(DecimalState, Char.is_digit(c), DecInt{},
        Bool.pick(DecimalState, Char.is_eq(c, '.'), DecDotAfterInt{},
          Bool.pick(DecimalState, is_exponent(c), DecExpStart{}, DecInvalid{})))
    case DecDotFirst{}:
      Bool.pick(DecimalState, Char.is_digit(c), DecFrac{}, DecInvalid{})
    case DecDotAfterInt{}:
      Bool.pick(DecimalState, Char.is_digit(c), DecFrac{},
        Bool.pick(DecimalState, is_exponent(c), DecExpStart{}, DecInvalid{}))
    case DecFrac{}:
      Bool.pick(DecimalState, Char.is_digit(c), DecFrac{},
        Bool.pick(DecimalState, is_exponent(c), DecExpStart{}, DecInvalid{}))
    case DecExpStart{}:
      Bool.pick(DecimalState, is_sign(c), DecExpSign{},
        Bool.pick(DecimalState, Char.is_digit(c), DecExpDigits{}, DecInvalid{}))
    case DecExpSign{}:
      Bool.pick(DecimalState, Char.is_digit(c), DecExpDigits{}, DecInvalid{})
    case DecExpDigits{}:
      Bool.pick(DecimalState, Char.is_digit(c), DecExpDigits{}, DecInvalid{})
    case DecInvalid{}:
      DecInvalid{}

def decimal_accept(state: DecimalState) -> Bool:
  match state:
    case DecInt{}: True{}
    case DecDotAfterInt{}: True{}
    case DecFrac{}: True{}
    case DecExpDigits{}: True{}
    case _: False{}

def decimal_scan(s: String, state: DecimalState) -> Bool:
  match s:
    case SNil{}: decimal_accept(state)
    case SCon{head, tail}:
      decimal_scan(tail, decimal_step(state, head))

def valid_f32(s: String) -> Bool:
  decimal_scan(s, DecStart{})

def has_as_nat(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case AsNat{} <> tail: True{}
    case head <> tail: has_as_nat(tail)

def has_as_bool(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case AsBool{} <> tail: True{}
    case head <> tail: has_as_bool(tail)

def has_as_f32(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case AsF32{} <> tail: True{}
    case head <> tail: has_as_f32(tail)

def find_one_of(items: List<&2, Item>) -> Maybe<&2, List<&2, String>>:
  match items:
    case Nil{}: None{}
    case OneOf{values} <> tail: Some{values}
    case head <> tail: find_one_of(tail)

def choice_accept(found: Maybe<&2, List<&2, String>>,
    value: String) -> Bool:
  match found:
    case None{}: True{}
    case Some{values}:
      List.contains(~String, ~String.eq, values, value)

def default_valid(kind: UsageKind, +attrs: List<&2, Item>,
    +value: String) -> Bool:
  match kind:
    case NegatableKind{}:
      valid_bool(value)
    case _:
      Bool.and(Bool.or(Bool.not(has_as_nat(attrs)), valid_nat(value)),
        Bool.and(Bool.or(Bool.not(has_as_u32(attrs)), valid_u32(value)),
          Bool.and(Bool.or(Bool.not(has_as_bool(attrs)), valid_bool(value)),
            Bool.and(Bool.or(Bool.not(has_as_f32(attrs)), valid_f32(value)),
              choice_accept(find_one_of(attrs), value)))))

def check_default(found: Maybe<&2, String>, kind: UsageKind,
    +attrs: List<&2, Item>, id: String, at: String) -> List<&2, Problem>:
  match found:
    case None{}:
      Nil{}
    case Some{+value}:
      when_problem(Bool.or(has_required(attrs),
        Bool.not(default_valid(kind, attrs, value))),
        BadDefault{at, id, value})

def positional_issue(+kind: UsageKind, +id: String,
    attrs: List<&2, Item>, rest_items: List<&2, Item>,
    +seen_optional: Bool, +seen_variadic: Bool, +at: String) ->
    List<&2, Problem>:
  Bool.pick(List<&2, Problem>,
    Bool.and(seen_optional, kind_required_pos(kind)),
    [BadPositional{at, id, "required positional follows an optional positional"}],
    Bool.pick(List<&2, Problem>,
      Bool.and(seen_variadic, kind_variadic_pos(kind)),
      [BadPositional{at, id, "more than one variadic positional"}],
      Bool.pick(List<&2, Problem>,
        Bool.and(seen_variadic, kind_optional_pos(kind)),
        [BadPositional{at, id, "optional positional follows a variadic positional"}],
        when_problem(Bool.and(kind_variadic_pos(kind),
          Bool.and(has_rest(attrs), has_pos_item(rest_items))),
          BadPositional{at, id, "rest must be on the last positional"}))))

def bare_issue(+kind: UsageKind, id: String, short: String,
    +attrs: List<&2, Item>, at: String) -> List<&2, Problem>:
  +bare_kind = kind_bare(kind)
  +has = has_bare(attrs)
  when_problem(Bool.or(
    Bool.and(bare_kind, Bool.or(Bool.not(has),
      Bool.not(String.is_empty(short)))),
    Bool.and(Bool.not(bare_kind), has)), NeedBare{at, id})

def misplaced_arg(+kind: UsageKind, +attrs: List<&2, Item>,
    +at: String) -> List<&2, Problem>:
  List.append(&2, Problem, placement_issues(attrs, kind, at),
    duplicate_type_issues(value_type_names(attrs), at))

type ArgCheck is Data:
  ArgCheck{issues: List<&2, Problem>, entries: List<&2, Seen>,
    optional: Bool, variadic: Bool}

def arg_reserved_dup(+at: String, +long: String, seen: List<&2, Seen>,
    id: String, short: String, version: Bool) -> List<&2, Problem>:
  reserved = Bool.or(String.eq(long, "--help"),
    Bool.and(version, String.eq(long, "--version")))
  Bool.pick(List<&2, Problem>, reserved,
    [Reserved{at, long}], maybe_dup(arg_collision(seen, id, short, long), at))

def arg_issues(+kind: UsageKind, +id: String, +short: String,
    +long: String, usage: String, help: String, +attrs: List<&2, Item>,
    remaining: List<&2, Item>, +at: String, ids: List<&2, String>,
    seen: List<&2, Seen>, optional: Bool, variadic: Bool,
    version: Bool) -> List<&2, Problem>:
  List.concat(&2, Problem, [
    arg_reserved_dup(at, long, seen, id, short, version),
    misplaced_arg(kind, attrs, at),
    when_problem(Bool.and(String.is_empty(help),
      Bool.not(has_hidden(attrs))), NoHelp{at, usage}),
    check_default(find_default(attrs), kind, attrs, id, at),
    missing_refs(List.append(&2, String,
      find_requires(attrs), find_conflicts(attrs)), ids, at),
    positional_issue(kind, id, attrs, remaining, optional, variadic, at),
    when_problem(bad_choices(attrs), BadChoices{at, id}),
    bare_issue(kind, id, short, attrs, at),
  ])

def arg_check(parsed: Usage, +usage: String, help: String,
    +attrs: List<&2, Item>, remaining: List<&2, Item>, +at: String,
    ids: List<&2, String>, +seen: List<&2, Seen>,
    +optional: Bool, +variadic: Bool, +version: Bool) -> ArgCheck:
  match parsed:
    case Invalid{col}:
      ArgCheck{List.append(&2, Problem, [BadUsage{at, usage, col}],
        when_problem(Bool.and(String.is_empty(help),
          Bool.not(has_hidden(attrs))), NoHelp{at, usage})),
        Nil{}, optional, variadic}
    case Parsed{derived, +short, +long, +kind}:
      +id = use_id(find_id(attrs), derived)
      +aliases = find_aliases(attrs)
      issues = List.append(&2, Problem,
        arg_issues(kind, id, short, long, usage, help, attrs,
          remaining, at, ids, seen, optional, variadic, version),
        arg_alias_issues(aliases, at, SeenArg{id, short, long} <> seen,
          version))
      ArgCheck{issues, SeenArg{id, short, long} <>
        arg_alias_entries(aliases),
        Bool.or(optional, kind_optional_pos(kind)),
        Bool.or(variadic, kind_variadic_pos(kind))}

def command_body_issues(+at: String, name: String, about: String,
    +items: List<&2, Item>) -> List<&2, Problem>:
  List.concat(&2, Problem, [
    when_problem(Bool.and(String.is_empty(about),
      Bool.not(has_hidden(items))), NoHelp{at, name}),
    when_problem(Bool.and(has_pos_item(items), has_sub_item(items)),
      Mixed{at}),
    missing_refs(scope_group_rules(items), scope_groups(items), at),
    missing_refs(scope_groups(items), scope_group_rules(items), at),
  ])

def sub_name_issues(+at: String, +name: String,
    seen: List<&2, Seen>) -> List<&2, Problem>:
  List.append(&2, Problem,
    when_problem(Bool.not(valid_command_name(name)), BadName{at, name}),
    Bool.pick(List<&2, Problem>, String.eq(name, "help"),
      [Reserved{at, name}],
      when_problem(sub_collision(seen, name), Dup{at, name})))

def item_count(items: List<&2, Item>) -> Nat:
  match items:
    case Nil{}:
      0n
    case Arg{usage, help, attrs} <> tail:
      Nat.add(1n, Nat.add(item_count(attrs), item_count(tail)))
    case Sub{name, about, children} <> tail:
      Nat.add(1n, Nat.add(item_count(children), item_count(tail)))
    case head <> tail:
      Nat.add(1n, item_count(tail))

type LintWork is Data:
  WorkItems{items: List<&2, Item>, at: String,
    ids: List<&2, String>, seen: List<&2, Seen>,
    optional: Bool, variadic: Bool, version: Bool, root: Bool}
  WorkAfterArg{check: ArgCheck, tail: List<&2, Item>, at: String,
    ids: List<&2, String>, seen: List<&2, Seen>,
    version: Bool, root: Bool}

def lint_work(fuel: Nat, work: LintWork) -> List<&2, Problem>:
  match fuel work:
    case 0n _:
      Nil{}
    case 1n+p WorkItems{Nil{}, at, ids, seen, optional, variadic, version, root}:
      Nil{}
    case 1n+p WorkItems{Arg{+usage, help, attrs} <> +tail,
        +at, +ids, +seen, optional, variadic, +version, root}:
      lint_work(p, WorkAfterArg{
        arg_check(parse_usage(usage), usage, help, attrs, tail,
          at, ids, seen, optional, variadic, version),
        tail, at, ids, seen, version, root})
    case 1n++p WorkItems{Sub{+name, about, +children} <> tail,
        +at, ids, +seen, optional, variadic, +version, root}:
      +child_at = String.concat([at, " ", name])
      +aliases = find_aliases(children)
      List.concat(&2, Problem, [
        sub_name_issues(at, name, seen),
        sub_alias_issues(aliases, at, SeenSub{name} <> seen),
        command_body_issues(child_at, name, about, children),
        lint_work(p, WorkItems{children, child_at, scope_ids(children),
          Nil{}, False{}, False{}, version, False{}}),
        lint_work(p, WorkItems{tail, at, ids,
          List.append(&2, Seen, sub_alias_entries(aliases),
            SeenSub{name} <> seen),
          optional, variadic, version, root}),
      ])
    case 1n+p WorkItems{head <> tail,
        +at, ids, seen, optional, variadic, version, +root}:
      List.append(&2, Problem,
        maybe_misplaced(command_attr_name(head, root), at),
        lint_work(p, WorkItems{tail, at, ids, seen, optional,
          variadic, version, root}))
    case 1n+p WorkAfterArg{ArgCheck{issues, entries, next_optional,
        next_variadic}, tail, at, ids, seen, version, root}:
      List.append(&2, Problem, issues,
        lint_work(p, WorkItems{tail, at, ids,
          List.append(&2, Seen, entries, seen),
          next_optional, next_variadic, version, root}))

def lint_items(+items: List<&2, Item>, at: String,
    ids: List<&2, String>, version: Bool, root: Bool) -> List<&2, Problem>:
  lint_work(Nat.add(1n, Nat.mul(4n, item_count(items))),
    WorkItems{items, at, ids, Nil{}, False{}, False{}, version, root})

def problems(c: Cmd) -> List<&2, Problem>:
  match c:
    case Cmd{+name, about, +items}:
      List.concat(&2, Problem, [
        when_problem(Bool.not(valid_command_name(name)), BadName{name, name}),
        command_body_issues(name, name, about, items),
        lint_items(items, name, scope_ids(items), has_version_item(items), True{}),
      ])
