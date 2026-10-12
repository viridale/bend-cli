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
  StripPlain{}
  StripEsc{}
  StripBody{pending: String}

def strip_go(s: String, state: StripState) -> String:
  match s:
    case SNil{}:
      match state:
        case StripPlain{}: ""
        case StripEsc{}: "\u{1B}"
        case StripBody{pending}: pending
    case SCon{+h, t}:
      match state:
        case StripPlain{}:
          +esc = Char.is_eq(h, '\u{1B}')
          String.append(Bool.pick(String, esc, "", Char.show(h)),
            strip_go(t, Bool.pick(StripState, esc, StripEsc{}, StripPlain{})))
        case StripEsc{}:
          +bracket = Char.is_eq(h, '[')
          +esc = Char.is_eq(h, '\u{1B}')
          +prefix = Bool.pick(String, bracket, "",
            Bool.pick(String, esc, "\u{1B}",
              String.append("\u{1B}", Char.show(h))))
          +next = Bool.pick(StripState, bracket, StripBody{"\u{1B}["},
            Bool.pick(StripState, esc, StripEsc{}, StripPlain{}))
          String.append(prefix, strip_go(t, next))
        case StripBody{+pending}:
          +end = Char.is_eq(h, 'm')
          +esc = Char.is_eq(h, '\u{1B}')
          +ok = sgr_body_char(h)
          +grown = String.append(pending, Char.show(h))
          +prefix = Bool.pick(String, end, "",
            Bool.pick(String, esc, pending,
              Bool.pick(String, ok, "", grown)))
          +next = Bool.pick(StripState, end, StripPlain{},
            Bool.pick(StripState, esc, StripEsc{},
              Bool.pick(StripState, ok, StripBody{grown}, StripPlain{})))
          String.append(prefix, strip_go(t, next))

def strip(s: String) -> String:
  strip_go(s, StripPlain{})

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

def code_width_by(small: Bool, +code: U32) -> Nat:
  match small:
    case True{}:
      Bool.pick(Nat, Bool.or(U32.is_le(code, 31),
        Bool.and(U32.is_ge(code, 127), U32.is_le(code, 159))), 0n, 1n)
    case False{}:
      Bool.pick(Nat, Bool.or(unicode_is_zero_mark(code),
        Bool.and(U32.is_ge(code, 8203), U32.is_le(code, 8207))), 0n,
        Bool.pick(Nat, unicode_is_wide(code), 2n, 1n))

def code_width(+code: U32) -> Nat:
  code_width_by(U32.is_lt(code, 768), code)

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

def words(s: String) -> List<&2, String>:
  List.filter(~String, ~(w => Bool.not(String.is_empty(w))),
    String.split(s, ' '))

def wrap_line(+line: String, cols: Nat) -> String:
  +indent = leading_indent(line)
  body = String.drop(line, String.length(indent))
  parts = words(body)
  wrap_words(parts, WrapState{indent, cols, indent, False{}, Nil{}})

def wrap_lines(lines: List<&2, String>, +cols: Nat) -> List<&2, String>:
  match lines:
    case Nil{}:
      Nil{}
    case head <> tail:
      wrap_line(head, cols) <> wrap_lines(tail, cols)

def wrap(text: String, cols: Nat) -> String:
  String.join(wrap_lines(String.lines(text), cols), "\n")

type ValueType is Data:
  TNat{}
  TU32{}
  TF32{}
  TBool{}
  TFile{}
  TDir{}

def type_name(t: ValueType) -> String:
  match t:
    case TNat{}: "as_nat"
    case TU32{}: "as_u32"
    case TF32{}: "as_f32"
    case TBool{}: "as_bool"
    case TFile{}: "as_file"
    case TDir{}: "as_dir"

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
  AttrDefault{value: String}
  AttrEnv{name: String}
  Global{}
  Heading{title: String}
  As{t: ValueType}
  OneOf{values: List<&2, String>}
  Delim{sep: Char}
  Hyphen{}
  Rest{}
  Bare{value: String}
  Conflicts{id: String}
  Requires{id: String}
  Group{name: String}
  Builtin{}

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
  AttrDefault{value}

def env(name: String) -> Item:
  AttrEnv{name}

def global() -> Item:
  Global{}

def heading(title: String) -> Item:
  Heading{title}

def as_nat() -> Item:
  As{TNat{}}

def as_u32() -> Item:
  As{TU32{}}

def as_f32() -> Item:
  As{TF32{}}

def as_bool() -> Item:
  As{TBool{}}

def as_file() -> Item:
  As{TFile{}}

def as_dir() -> Item:
  As{TDir{}}

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

# Builtin{} marks the subcommands that only eval acts on (§6.4).
def completions() -> Item:
  sub("completions", "Print a shell completion script", [Builtin{}, arg("<SHELL>", "Shell to generate for", [one_of(["bash", "zsh", "fish"])])])

def man() -> Item:
  sub("man", "Print the man page", [Builtin{}, hidden(), arg("[COMMAND]...", "Subcommand path", [])])

type UsageKind is Data:
  FlagKind{}
  CountKind{}
  NegatableKind{}
  OptionKind{many: Bool}
  BareOptionKind{}
  PosKind{required: Bool, many: Bool}

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
        PosKind{True{}, repeat})
    case SCon{Chr{91}, tail}:
      finish_pos(scan_ph(tail, 1n, "", ']'),
        PosKind{False{}, repeat})
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
          OptionKind{repeat}))
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
        OptionKind{repeat})
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
    case PosKind{required, many}: True{}
    case _: False{}

def kind_optional_pos(kind: UsageKind) -> Bool:
  match kind:
    case PosKind{required, many}: Bool.not(required)
    case _: False{}

def kind_variadic_pos(kind: UsageKind) -> Bool:
  match kind:
    case PosKind{required, many}: many
    case _: False{}

def kind_required_pos(kind: UsageKind) -> Bool:
  match kind:
    case PosKind{required, many}: required
    case _: False{}

def kind_valued(kind: UsageKind) -> Bool:
  match kind:
    case OptionKind{many}: True{}
    case BareOptionKind{}: True{}
    case PosKind{required, many}: True{}
    case _: False{}

def kind_bare(kind: UsageKind) -> Bool:
  match kind:
    case BareOptionKind{}: True{}
    case _: False{}

def kind_default_allowed(kind: UsageKind) -> Bool:
  match kind:
    case OptionKind{many}: True{}
    case BareOptionKind{}: True{}
    case PosKind{required, many}: Bool.not(required)
    case NegatableKind{}: True{}
    case _: False{}

def kind_required_allowed(kind: UsageKind) -> Bool:
  match kind:
    case OptionKind{many}: True{}
    case _: False{}

def kind_delim_allowed(kind: UsageKind) -> Bool:
  match kind:
    case OptionKind{many}: many
    case PosKind{required, many}: many
    case _: False{}

def bad_attr(cond: Bool, name: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, cond, Some{name}, None{})

def misplaced_attr_name(attr: Item, +kind: UsageKind) ->
    Maybe<&2, String>:
  match attr:
    case Global{}: bad_attr(kind_pos(kind), "global")
    case Rest{}: bad_attr(Bool.not(kind_variadic_pos(kind)), "rest")
    case AttrDefault{value}:
      bad_attr(Bool.not(kind_default_allowed(kind)), "default")
    case Required{}:
      bad_attr(Bool.not(kind_required_allowed(kind)), "required")
    case Heading{title}: bad_attr(kind_pos(kind), "heading")
    case Alias{name}: bad_attr(kind_pos(kind), "alias")
    case As{t}: bad_attr(Bool.not(kind_valued(kind)), type_name(t))
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
    case As{t} <> tail: type_name(t) <> value_type_names(tail)
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
    case AttrDefault{value}: Some{"default"}
    case AttrEnv{name}: Some{"env"}
    case Global{}: Some{"global"}
    case Heading{title}: Some{"heading"}
    case As{t}: Some{type_name(t)}
    case OneOf{values}: Some{"one_of"}
    case Delim{sep}: Some{"delim"}
    case Hyphen{}: Some{"hyphen"}
    case Rest{}: Some{"rest"}
    case Bare{value}: Some{"bare"}
    case Conflicts{id}: Some{"conflicts"}
    case Requires{id}: Some{"requires"}
    case Group{name}: Some{"group"}
    case Builtin{}: None{}

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

def has_builtin(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Builtin{} <> tail: True{}
    case head <> tail: has_builtin(tail)

def has_bare(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Bare{value} <> tail: True{}
    case head <> tail: has_bare(tail)

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
    case AttrDefault{value} <> tail: Some{value}
    case head <> tail: find_default(tail)

def find_delim(attrs: List<&2, Item>) -> Maybe<&2, Char>:
  match attrs:
    case Nil{}: None{}
    case Delim{sep} <> tail: Some{sep}
    case head <> tail: find_delim(tail)

def split_each(values: List<&2, String>, +sep: Char) ->
    List<&2, String>:
  match values:
    case Nil{}: Nil{}
    case head <> tail:
      List.append(&2, String, String.split(head, sep),
        split_each(tail, sep))

def apply_delim(found: Maybe<&2, Char>,
    values: List<&2, String>) -> List<&2, String>:
  match found:
    case None{}: values
    case Some{sep}: split_each(values, sep)

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

def usage_kind(~f: UsageKind -> Bool, parsed: Usage) -> Bool:
  match parsed:
    case Parsed{id, short, long, kind}: f(kind)
    case Invalid{col}: False{}

def has_pos_item(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Arg{usage, help, attrs} <> tail:
      Bool.or(usage_kind(~kind_pos, parse_usage(usage)), has_pos_item(tail))
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

def arg_entries(parsed: Usage, +attrs: List<&2, Item>) -> List<&2, Seen>:
  match parsed:
    case Parsed{derived, short, long, kind}:
      SeenArg{use_id(find_id(attrs), derived), short, long} <>
        arg_alias_entries(find_aliases(attrs))
    case Invalid{col}:
      Nil{}

def has_global(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Global{} <> tail: True{}
    case head <> tail: has_global(tail)

def global_entries(items: List<&2, Item>) -> List<&2, Seen>:
  match items:
    case Nil{}: Nil{}
    case Arg{+usage, help, +attrs} <> tail:
      List.append(&2, Seen,
        Bool.pick(List<&2, Seen>, has_global(attrs),
          arg_entries(parse_usage(usage), attrs), Nil{}),
        global_entries(tail))
    case head <> tail: global_entries(tail)

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

def find_one_of(items: List<&2, Item>) -> Maybe<&2, List<&2, String>>:
  match items:
    case Nil{}: None{}
    case OneOf{values} <> tail: Some{values}
    case head <> tail: find_one_of(tail)

# The first element of a value that fails to convert, and why.
type Bad is Data:
  Bad{value: String, reason: String}

def find_as(attrs: List<&2, Item>) -> Maybe<&2, ValueType>:
  match attrs:
    case Nil{}: None{}
    case As{kind} <> tail: Some{kind}
    case head <> tail: find_as(tail)

def type_reason(kind: ValueType, value: String) -> Maybe<&2, String>:
  match kind:
    case TNat{}:
      Bool.pick(Maybe<&2, String>, valid_nat(value), None{},
        Some{"expected a whole number from 0 to 281474976710655"})
    case TU32{}:
      Bool.pick(Maybe<&2, String>, valid_u32(value), None{},
        Some{"expected a whole number from 0 to 4294967295"})
    case TF32{}:
      Bool.pick(Maybe<&2, String>, valid_f32(value), None{},
        Some{"expected a decimal number"})
    case TBool{}:
      Bool.pick(Maybe<&2, String>, valid_bool(value), None{},
        Some{"expected true or false"})
    case TFile{}: None{}
    case TDir{}: None{}

def quoted_choices(values: List<&2, String>) -> List<&2, String>:
  match values:
    case Nil{}: Nil{}
    case head <> tail:
      String.concat(["'", head, "'"]) <> quoted_choices(tail)

def choices_reason(values: List<&2, String>) -> String:
  String.append("expected one of ",
    String.join(quoted_choices(values), ", "))

def choice_reason(found: Maybe<&2, List<&2, String>>,
    value: String) -> Maybe<&2, String>:
  match found:
    case None{}: None{}
    case Some{+values}:
      Bool.pick(Maybe<&2, String>,
        List.contains(~String, ~String.eq, values, value),
        None{}, Some{choices_reason(values)})

def reason_from_type(found: Maybe<&2, ValueType>,
    value: String) -> Maybe<&2, String>:
  match found:
    case None{}: None{}
    case Some{kind}: type_reason(kind, value)

def first_reason(found: Maybe<&2, String>,
    other: Maybe<&2, String>) -> Maybe<&2, String>:
  match found:
    case None{}: other
    case Some{reason}: Some{reason}

def value_reason(+attrs: List<&2, Item>, +value: String) ->
    Maybe<&2, String>:
  first_reason(reason_from_type(find_as(attrs), value),
    choice_reason(find_one_of(attrs), value))

def bad_value(reason: Maybe<&2, String>, value: String) ->
    Maybe<&2, Bad>:
  match reason:
    case None{}: None{}
    case Some{why}: Some{Bad{value, why}}

def first_bad(values: List<&2, String>, +attrs: List<&2, Item>) ->
    Maybe<&2, Bad>:
  match values:
    case Nil{}: None{}
    case +head <> tail:
      Maybe.or(&2, Bad, bad_value(value_reason(attrs, head), head),
        first_bad(tail, attrs))

def split_bad(found: Maybe<&2, Char>, attrs: List<&2, Item>,
    +value: String) -> Maybe<&2, Bad>:
  match found:
    case None{}: bad_value(value_reason(attrs, value), value)
    case Some{sep}: first_bad(String.split(value, sep), attrs)

# A delimited value splits first; the first element that fails (§8.2).
def value_bad(+attrs: List<&2, Item>, value: String) -> Maybe<&2, Bad>:
  split_bad(find_delim(attrs), attrs, value)

# A value from env or a default converts each element on its own (§8.2).
def value_issue(kind: UsageKind, attrs: List<&2, Item>,
    +value: String) -> Maybe<&2, Bad>:
  match kind:
    case FlagKind{}: bad_value(type_reason(TBool{}, value), value)
    case NegatableKind{}: bad_value(type_reason(TBool{}, value), value)
    case CountKind{}: bad_value(type_reason(TNat{}, value), value)
    case _: value_bad(attrs, value)

def bad_default(required: Bool, issue: Maybe<&2, Bad>, value: String,
    id: String, at: String) -> List<&2, Problem>:
  match required issue:
    case True{} _: [BadDefault{at, id, value}]
    case False{} Some{Bad{bad, why}}: [BadDefault{at, id, bad}]
    case False{} None{}: Nil{}

def check_default(found: Maybe<&2, String>, kind: UsageKind,
    +attrs: List<&2, Item>, id: String, at: String) -> List<&2, Problem>:
  match found:
    case None{}:
      Nil{}
    case Some{+value}:
      bad_default(has_required(attrs), value_issue(kind, attrs, value),
        value, id, at)

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

def arg_problems(parsed: Usage, +usage: String, help: String,
    +attrs: List<&2, Item>, remaining: List<&2, Item>, +at: String,
    ids: List<&2, String>, +seen: List<&2, Seen>,
    optional: Bool, variadic: Bool, +version: Bool) -> List<&2, Problem>:
  match parsed:
    case Invalid{col}:
      List.append(&2, Problem, [BadUsage{at, usage, col}],
        when_problem(Bool.and(String.is_empty(help),
          Bool.not(has_hidden(attrs))), NoHelp{at, usage}))
    case Parsed{derived, +short, +long, +kind}:
      +id = use_id(find_id(attrs), derived)
      +aliases = find_aliases(attrs)
      List.append(&2, Problem,
        arg_issues(kind, id, short, long, usage, help, attrs,
          remaining, at, ids, seen, optional, variadic, version),
        arg_alias_issues(aliases, at, SeenArg{id, short, long} <> seen,
          version))

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

def lint(items: List<&2, Item>, +at: String, +ids: List<&2, String>,
    +seen: List<&2, Seen>, +inherited: List<&2, Seen>, +optional: Bool,
    +variadic: Bool, +version: Bool, +root: Bool) -> List<&2, Problem>:
  match items:
    case Nil{}:
      Nil{}
    case Arg{+usage, help, +attrs} <> +tail:
      +parsed = parse_usage(usage)
      List.append(&2, Problem,
        arg_problems(parsed, usage, help, attrs, tail, at, ids, seen,
          optional, variadic, version),
        lint(tail, at, ids,
          List.append(&2, Seen, arg_entries(parsed, attrs), seen),
          inherited,
          Bool.or(optional, usage_kind(~kind_optional_pos, parsed)),
          Bool.or(variadic, usage_kind(~kind_variadic_pos, parsed)),
          version, root))
    case Sub{+name, about, +children} <> tail:
      +child_at = String.concat([at, " ", name])
      +aliases = find_aliases(children)
      List.concat(&2, Problem, [
        sub_name_issues(at, name, seen),
        sub_alias_issues(aliases, at, SeenSub{name} <> seen),
        command_body_issues(child_at, name, about, children),
        lint(children, child_at, scope_ids(children), inherited,
          List.append(&2, Seen, global_entries(children), inherited),
          False{}, False{}, version, False{}),
        lint(tail, at, ids,
          List.append(&2, Seen, sub_alias_entries(aliases),
            SeenSub{name} <> seen),
          inherited, optional, variadic, version, root),
      ])
    case head <> tail:
      List.append(&2, Problem,
        maybe_misplaced(command_attr_name(head, root), at),
        lint(tail, at, ids, seen, inherited, optional, variadic,
          version, root))

def problems(c: Cmd) -> List<&2, Problem>:
  match c:
    case Cmd{+name, about, +items}:
      List.concat(&2, Problem, [
        when_problem(Bool.not(valid_command_name(name)), BadName{name, name}),
        command_body_issues(name, name, about, items),
        lint(items, name, scope_ids(items), Nil{}, global_entries(items),
          False{}, False{}, has_version_item(items), True{}),
      ])

type Src is Data:
  Argv{}
  Env{}
  Default{}
  Absent{}

type Var is Data:
  Var{name: String, value: String}

type Host is Data:
  Host{width: Nat, vars: List<&2, Var>, out_tty: Bool, err_tty: Bool}

type Field is Data:
  Field{id: String, values: List<&2, String>, source: Src}

type ScanEvent is Data:
  FlagHit{id: String, value: Bool}
  CountHit{id: String}
  ValueHit{id: String, value: String}
  Operand{token: String}
  Enter{name: String}
  HelpHit{long: Bool}
  VersionHit{}

type ScanFault is Data:
  E01{token: String}
  E02{name: String}
  E03{arg: String}
  E04{arg: String, value: String, reason: String}
  E05{arg: String, value: String}
  E06{missing: List<&2, String>}
  E07{a: String, b: String}
  E08{a: String, b: String}
  E09{token: String}
  E10{}
  E11{arg: String, value: String, name: String, reason: String}

type ExternalArgs is Data:
  ExternalArgs{name: String, args: List<&2, String>}

type ScanTrace is Data:
  ScanTrace{path: List<&2, String>, events: List<&2, ScanEvent>,
    ended: Bool, external: Maybe<&2, ExternalArgs>,
    issue: Maybe<&2, ScanFault>}

type ParseResult is Data:
  Accepted{path: List<&2, String>, fields: List<&2, Field>,
    external: Maybe<&2, ExternalArgs>}
  Rejected{path: List<&2, String>, fault: ScanFault}
  HelpRequested{path: List<&2, String>, long: Bool}
  VersionRequested{}
  SummaryRequired{}

type Early is Data:
  EarlyHelp{long: Bool}
  EarlyVersion{}

type Gather is Data:
  Gather{seen: Bool, values: List<&2, String>, count: Nat}

type FieldBuild is Data:
  Built{fields: List<&2, Field>}
  BuildFault{fault: ScanFault}

type EnvValue is Data:
  EnvValue{name: String, value: String}

def host(width: Nat) -> Host:
  Host{width, [], False{}, False{}}

def host_var(h: Host, name: String, value: String) -> Host:
  match h:
    case Host{width, vars, out_tty, err_tty}:
      Host{width, Var{name, value} <> vars, out_tty, err_tty}

def var_value(vars: List<&2, Var>, +name: String) -> Maybe<&2, String>:
  match vars:
    case Nil{}: None{}
    case Var{key, value} <> tail:
      Bool.pick(Maybe<&2, String>, String.eq(key, name),
        Some{value}, var_value(tail, name))

def host_value(h: Host, name: String) -> Maybe<&2, String>:
  match h:
    case Host{width, vars, out_tty, err_tty}:
      var_value(vars, name)

type ArgInfo is Data:
  ArgInfo{id: String, usage: String, short: String, long: String,
    kind: UsageKind, attrs: List<&2, Item>}

type OptFound is Data:
  OptFound{arg: ArgInfo, polarity: Bool}

type SubFound is Data:
  SubFound{name: String, items: List<&2, Item>}

type Scope is Data:
  Scope{path: List<&2, String>, items: List<&2, Item>,
    globals: List<&2, Item>}

type ScanState is Data:
  ScanState{scope: Scope, events: List<&2, ScanEvent>,
    resting: Bool, positional_count: Nat,
    external: Maybe<&2, ExternalArgs>, issue: Maybe<&2, ScanFault>}

# Phases after which no token is an operand and `--` is plain.
type Tail is Data:
  Faulted{state: ScanState}
  Walk{state: ScanState}
  Stopped{state: ScanState}

type Mode is Data:
  Open{state: ScanState}
  Fetch{state: ScanState, info: ArgInfo}
  Operands{state: ScanState, ended: Bool}
  Capture{state: ScanState, name: String}
  Closed{tail: Tail}

def arg_info_parsed(parsed: Usage, usage: String,
    +attrs: List<&2, Item>) -> ArgInfo:
  match parsed:
    case Parsed{derived, short, long, kind}:
      ArgInfo{use_id(find_id(attrs), derived), usage, short, long,
        kind, attrs}
    case Invalid{col}:
      ArgInfo{"", usage, "", "", FlagKind{}, attrs}

def arg_info(+usage: String, attrs: List<&2, Item>) -> ArgInfo:
  arg_info_parsed(parse_usage(usage), usage, attrs)

def arg_display(info: ArgInfo) -> String:
  match info:
    case ArgInfo{id, +usage, +short, long, kind, attrs}:
      Bool.pick(String, Bool.and(Bool.not(String.is_empty(short)),
        Bool.not(String.is_empty(long))),
        String.drop(usage, Nat.add(String.length(short), 2n)), usage)

def global_items(items: List<&2, Item>) -> List<&2, Item>:
  match items:
    case Nil{}: Nil{}
    case Arg{usage, help, +attrs} <> tail:
      +rest = global_items(tail)
      Bool.pick(List<&2, Item>, has_global(attrs),
        Arg{usage, help, attrs} <> rest, rest)
    case head <> tail: global_items(tail)

def kind_negatable(kind: UsageKind) -> Bool:
  match kind:
    case NegatableKind{}: True{}
    case _: False{}

def negated_long(long: String) -> String:
  String.append("--no-", String.drop(long, 2n))

def option_matches(+query: String, info: ArgInfo) ->
    Maybe<&2, OptFound>:
  match info:
    case ArgInfo{id, usage, +short, +long, +kind, +attrs}:
      +named = Bool.or(
        Bool.and(Bool.not(String.is_empty(short)), String.eq(query, short)),
        Bool.or(Bool.and(Bool.not(String.is_empty(long)),
          String.eq(query, long)),
          List.contains(~String, ~String.eq, find_aliases(attrs), query)))
      +negated = Bool.and(kind_negatable(kind),
        Bool.and(Bool.not(String.is_empty(long)),
          String.eq(query, negated_long(long))))
      Bool.pick(Maybe<&2, OptFound>, Bool.or(named, negated),
        Some{OptFound{ArgInfo{id, usage, short, long, kind, attrs},
          Bool.not(negated)}}, None{})

def find_option(items: List<&2, Item>, +query: String) ->
    Maybe<&2, OptFound>:
  match items:
    case Nil{}: None{}
    case Arg{usage, help, attrs} <> tail:
      +found = option_matches(query, arg_info(usage, attrs))
      Bool.pick(Maybe<&2, OptFound>,
        Maybe.is_some(&2, OptFound, found), found,
        find_option(tail, query))
    case head <> tail: find_option(tail, query)

def find_option_scope(scope: Scope, +query: String) ->
    Maybe<&2, OptFound>:
  match scope:
    case Scope{path, items, globals}:
      +found = find_option(items, query)
      Bool.pick(Maybe<&2, OptFound>,
        Maybe.is_some(&2, OptFound, found), found,
        find_option(globals, query))

def find_sub(items: List<&2, Item>, +query: String) ->
    Maybe<&2, SubFound>:
  match items:
    case Nil{}: None{}
    case Sub{+name, about, +children} <> tail:
      Bool.pick(Maybe<&2, SubFound>,
        Bool.or(String.eq(query, name),
          List.contains(~String, ~String.eq,
            find_aliases(children), query)),
        Some{SubFound{name, children}}, find_sub(tail, query))
    case head <> tail: find_sub(tail, query)

def has_external(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case External{} <> tail: True{}
    case head <> tail: has_external(tail)

def has_sub_optional(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case SubOptional{} <> tail: True{}
    case head <> tail: has_sub_optional(tail)

def positional_items(items: List<&2, Item>) -> List<&2, Item>:
  match items:
    case Nil{}: Nil{}
    case Arg{+usage, +help, +attrs} <> tail:
      +rest = positional_items(tail)
      Bool.pick(List<&2, Item>,
        usage_kind(~kind_pos, parse_usage(usage)),
        Arg{usage, help, attrs} <> rest, rest)
    case head <> tail: positional_items(tail)

def has_variadic_pos(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Arg{usage, help, attrs} <> tail:
      Bool.or(usage_kind(~kind_variadic_pos, parse_usage(usage)),
        has_variadic_pos(tail))
    case head <> tail: has_variadic_pos(tail)

def positional_can_take(items: List<&2, Item>, count: Nat) -> Bool:
  +slots = positional_items(items)
  Bool.or(Nat.is_lt(count, List.length(&2, Item, slots)),
    has_variadic_pos(slots))

def next_positional_slot(slots: List<&2, Item>, +count: Nat) ->
    Maybe<&2, ArgInfo>:
  match slots:
    case Nil{}: None{}
    case Arg{+usage, help, attrs} <> tail:
      Bool.pick(Maybe<&2, ArgInfo>,
        Bool.or(Nat.is_eq(count, 0n),
          usage_kind(~kind_variadic_pos, parse_usage(usage))),
        Some{arg_info(usage, attrs)},
        next_positional_slot(tail, Nat.sub(count, 1n)))
    case head <> tail: next_positional_slot(tail, count)

def scope_next_slot(scope: Scope, count: Nat) -> Maybe<&2, ArgInfo>:
  match scope:
    case Scope{path, items, globals}:
      next_positional_slot(positional_items(items), count)

def scan_start(c: Cmd) -> ScanState:
  match c:
    case Cmd{name, about, items}:
      ScanState{Scope{[], items, []}, [], False{}, 0n, None{}, None{}}

def scan_event(state: ScanState, event: ScanEvent) -> ScanState:
  match state:
    case ScanState{scope, events, resting, positional_count,
        external, issue}:
      ScanState{scope, event <> events, resting,
        positional_count, external, issue}

def first_issue(issue: Maybe<&2, ScanFault>, fault: ScanFault) ->
    Maybe<&2, ScanFault>:
  match issue:
    case None{}: Some{fault}
    case Some{old}: Some{old}

def scan_error(state: ScanState, fault: ScanFault) -> ScanState:
  match state:
    case ScanState{scope, events, resting, positional_count,
        external, issue}:
      ScanState{scope, events, resting, positional_count,
        external, first_issue(issue, fault)}

def has_hyphen(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Hyphen{} <> tail: True{}
    case head <> tail: has_hyphen(tail)

def slot_rest(found: Maybe<&2, ArgInfo>) -> Bool:
  match found:
    case None{}: False{}
    case Some{ArgInfo{id, usage, short, long, kind, attrs}}:
      has_rest(attrs)

def slot_hyphen(found: Maybe<&2, ArgInfo>) -> Bool:
  match found:
    case None{}: False{}
    case Some{ArgInfo{id, usage, short, long, kind, attrs}}:
      has_hyphen(attrs)

def has_as_f32(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case As{TF32{}} <> tail: True{}
    case head <> tail: has_as_f32(tail)

def slot_f32(found: Maybe<&2, ArgInfo>) -> Bool:
  match found:
    case None{}: False{}
    case Some{ArgInfo{id, usage, short, long, kind, attrs}}:
      has_as_f32(attrs)

def is_negative_number(+s: String) -> Bool:
  Bool.and(String.starts_with(s, "-"), valid_f32(s))

def before_equal(s: String) -> String:
  match s:
    case SNil{}: SNil{}
    case SCon{Chr{61}, tail}: SNil{}
    case SCon{head, tail}: SCon{head, before_equal(tail)}

def after_equal(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}: None{}
    case SCon{Chr{61}, tail}: Some{tail}
    case SCon{head, tail}: after_equal(tail)

def first_option_name(+token: String) -> String:
  Bool.pick(String, String.starts_with(token, "--"),
    before_equal(token), String.take(token, 2n))

def scope_option_known(scope: Scope, token: String) -> Bool:
  Maybe.is_some(&2, OptFound,
    find_option_scope(scope, first_option_name(token)))

def scope_builtin_known(scope: Scope, +token: String) -> Bool:
  match scope:
    case Scope{path, items, globals}:
      +name = first_option_name(token)
      Bool.or(String.eq(name, "-h"),
        Bool.or(String.eq(name, "--help"),
          Bool.and(List.is_empty(&2, String, path),
            Bool.and(has_version_item(items),
              Bool.or(String.eq(name, "-V"),
                String.eq(name, "--version"))))))

def scope_any_option_known(+scope: Scope, +token: String) -> Bool:
  Bool.or(scope_option_known(scope, token),
    scope_builtin_known(scope, token))

def scan_operand_ok(state: ScanState, token: String) -> ScanState:
  match state:
    case ScanState{+scope, events, resting, +positional_count,
        external, issue}:
      ScanState{scope, Operand{token} <> events,
        Bool.or(resting,
          slot_rest(scope_next_slot(scope, positional_count))),
        Nat.add(positional_count, 1n), external, issue}

def scan_operand_case(allowed: Bool, state: ScanState,
    token: String) -> ScanState:
  match allowed:
    case True{}: scan_operand_ok(state, token)
    case False{}: scan_error(state, E09{token})

def scope_can_take(scope: Scope, count: Nat) -> Bool:
  match scope:
    case Scope{path, items, globals}:
      positional_can_take(items, count)

def scan_operand(state: ScanState, token: String) -> ScanState:
  match state:
    case ScanState{+scope, events, resting, +positional_count,
        external, issue}:
      scan_operand_case(scope_can_take(scope, positional_count),
        ScanState{scope, events, resting, positional_count,
          external, issue}, token)

def scan_descend(state: ScanState, sub: SubFound) -> ScanState:
  match state:
    case ScanState{scope, events, resting, positional_count,
        external, issue}:
      match scope:
        case Scope{path, items, globals}:
          match sub:
            case SubFound{+name, children}:
              ScanState{Scope{
                List.append(&2, String, path, [name]), children,
                List.append(&2, Item, global_items(items), globals)},
                Enter{name} <> events, resting, 0n,
                external, issue}

def scan_external(state: ScanState, name: String,
    args: List<&2, String>) -> ScanState:
  match state:
    case ScanState{scope, events, resting, positional_count,
        external, issue}:
      ScanState{scope, events, resting, positional_count,
        Some{ExternalArgs{name, args}}, issue}

def info_attrs(info: ArgInfo) -> List<&2, Item>:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}: attrs

# E04 quotes the first element that fails.
def scan_value_result(found: Maybe<&2, Bad>, state: ScanState,
    info: ArgInfo, value: String) -> ScanState:
  match found:
    case None{}:
      match info:
        case ArgInfo{id, usage, short, long, kind, attrs}:
          scan_event(state, ValueHit{id, value})
    case Some{Bad{bad, why}}:
      scan_error(state, E04{arg_display(info), bad, why})

def scan_value(state: ScanState, +info: ArgInfo,
    +value: String) -> ScanState:
  scan_value_result(value_bad(info_attrs(info), value), state, info, value)

def scan_simple_hit(state: ScanState, info: ArgInfo,
    polarity: Bool) -> ScanState:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}:
      match kind:
        case CountKind{}: scan_event(state, CountHit{id})
        case _: scan_event(state, FlagHit{id, polarity})

def scan_settle_case(resting: Bool, issue: Maybe<&2, ScanFault>,
    scope: Scope, events: List<&2, ScanEvent>, positional_count: Nat,
    external: Maybe<&2, ExternalArgs>) -> Mode:
  match resting issue:
    case True{} None{}:
      Operands{ScanState{scope, events, True{}, positional_count, external,
        None{}}, False{}}
    case True{} Some{fault}:
      Operands{ScanState{scope, events, True{}, positional_count, external,
        Some{fault}}, False{}}
    case False{} None{}:
      Open{ScanState{scope, events, False{}, positional_count, external,
        None{}}}
    case False{} Some{fault}:
      Closed{Faulted{ScanState{scope, events, False{}, positional_count,
        external, Some{fault}}}}

def scan_settle(state: ScanState) -> Mode:
  match state:
    case ScanState{scope, events, resting, positional_count, external,
        issue}:
      scan_settle_case(resting, issue, scope, events, positional_count,
        external)

def scan_faulted(+state: ScanState, +token: String) -> Tail:
  Bool.pick(Tail, String.eq(token, "--help"),
    Stopped{scan_event(state, HelpHit{True{}})},
    Bool.pick(Tail, String.eq(token, "-h"),
      Stopped{scan_event(state, HelpHit{False{}})},
      Faulted{state}))

def short_digit(short: String) -> Bool:
  match short:
    case SCon{Chr{45}, SCon{head, tail}}: Char.is_digit(head)
    case _: False{}

def usage_digit_short(parsed: Usage) -> Bool:
  match parsed:
    case Parsed{id, short, long, kind}: short_digit(short)
    case Invalid{col}: False{}

def items_digit_short(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Arg{usage, help, attrs} <> tail:
      Bool.or(usage_digit_short(parse_usage(usage)),
        items_digit_short(tail))
    case head <> tail: items_digit_short(tail)

def scope_digit_short(scope: Scope) -> Bool:
  match scope:
    case Scope{path, items, globals}:
      Bool.or(items_digit_short(items), items_digit_short(globals))

def arg_has_hyphen(info: ArgInfo) -> Bool:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}:
      has_hyphen(attrs)

def arg_is_f32(info: ArgInfo) -> Bool:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}:
      has_as_f32(attrs)

def fetch_allowed(scope: Scope, +info: ArgInfo,
    +token: String) -> Bool:
  Bool.and(Bool.not(String.eq(token, "--")),
    Bool.or(Bool.not(String.starts_with(token, "-")),
      Bool.or(String.eq(token, "-"),
        Bool.or(arg_has_hyphen(info),
          Bool.and(arg_is_f32(info),
            Bool.and(is_negative_number(token),
              Bool.not(scope_digit_short(scope))))))))

def scan_fetch_result(allowed: Bool, state: ScanState,
    info: ArgInfo, token: String) -> Mode:
  match allowed:
    case True{}: scan_settle(scan_value(state, info, token))
    case False{}:
      Closed{scan_faulted(scan_error(state, E03{arg_display(info)}), token)}

def scan_state_scope(state: ScanState) -> Scope:
  match state:
    case ScanState{scope, events, resting, positional_count,
        external, issue}: scope

def scan_fetch(+state: ScanState, +info: ArgInfo,
    +token: String) -> Mode:
  scan_fetch_result(fetch_allowed(scan_state_scope(state), info, token),
    state, info, token)

def bare_value(attrs: List<&2, Item>) -> String:
  match attrs:
    case Nil{}: ""
    case Bare{value} <> tail: value
    case head <> tail: bare_value(tail)

def scan_option(attached: Maybe<&2, String>, state: ScanState,
    info: ArgInfo) -> Mode:
  match attached:
    case Some{value}: scan_settle(scan_value(state, info, value))
    case None{}: Fetch{state, info}

def info_bare_value(info: ArgInfo) -> String:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}:
      bare_value(attrs)

def scan_bare_option(attached: Maybe<&2, String>, state: ScanState,
    +info: ArgInfo) -> Mode:
  match attached:
    case Some{value}: scan_settle(scan_value(state, info, value))
    case None{}:
      scan_settle(scan_value(state, info, info_bare_value(info)))

def scan_simple_option(attached: Maybe<&2, String>, state: ScanState,
    info: ArgInfo, polarity: Bool) -> Mode:
  match attached:
    case Some{value}:
      scan_settle(scan_error(state, E05{arg_display(info), value}))
    case None{}: scan_settle(scan_simple_hit(state, info, polarity))

def info_kind(info: ArgInfo) -> UsageKind:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}: kind

def scan_found_kind(kind: UsageKind, attached: Maybe<&2, String>,
    state: ScanState, info: ArgInfo, polarity: Bool) -> Mode:
  match kind:
    case FlagKind{}:
      scan_simple_option(attached, state, info, polarity)
    case CountKind{}:
      scan_simple_option(attached, state, info, polarity)
    case NegatableKind{}:
      scan_simple_option(attached, state, info, polarity)
    case OptionKind{many}:
      scan_option(attached, state, info)
    case BareOptionKind{}:
      scan_bare_option(attached, state, info)
    case PosKind{required, many}:
      scan_settle(state)

def scan_found(found: OptFound, attached: Maybe<&2, String>,
    state: ScanState) -> Mode:
  match found:
    case OptFound{+arg, polarity}:
      scan_found_kind(info_kind(arg), attached, state, arg, polarity)

def scope_version(scope: Scope) -> Bool:
  match scope:
    case Scope{path, items, globals}:
      Bool.and(List.is_empty(&2, String, path), has_version_item(items))

def scan_builtin_hit(attached: Maybe<&2, String>, state: ScanState,
    event: ScanEvent, name: String) -> Mode:
  match attached:
    case Some{value}: scan_settle(scan_error(state, E05{name, value}))
    case None{}: Closed{Stopped{scan_event(state, event)}}

def scan_builtin_version(enabled: Bool, attached: Maybe<&2, String>,
    state: ScanState) -> Mode:
  match enabled:
    case True{}:
      scan_builtin_hit(attached, state, VersionHit{}, "--version")
    case False{}:
      scan_settle(scan_error(state, E01{"--version"}))

def scan_builtin_long(+name: String, +attached: Maybe<&2, String>,
    +state: ScanState) -> Mode:
  Bool.pick(Mode, String.eq(name, "--help"),
    scan_builtin_hit(attached, state, HelpHit{True{}}, "--help"),
    Bool.pick(Mode, String.eq(name, "--version"),
      scan_builtin_version(scope_version(scan_state_scope(state)),
        attached, state),
      scan_settle(scan_error(state, E01{name}))))

def scan_long_found(found: Maybe<&2, OptFound>, name: String,
    attached: Maybe<&2, String>, state: ScanState) -> Mode:
  match found:
    case Some{option}: scan_found(option, attached, state)
    case None{}: scan_builtin_long(name, attached, state)

def scan_long(+token: String, +state: ScanState) -> Mode:
  +name = before_equal(token)
  scan_long_found(find_option_scope(scan_state_scope(state), name),
    name, after_equal(token), state)

def find_short_for_head(chars: String, state: ScanState) ->
    Maybe<&2, OptFound>:
  match chars:
    case SNil{}: None{}
    case SCon{head, tail}:
      find_option_scope(scan_state_scope(state),
        String.append("-", Char.show(head)))

def short_attached(chars: String) -> String:
  match chars:
    case SCon{Chr{61}, tail}: tail
    case _: chars

def scan_short_value_attached(value: String, state: ScanState,
    info: ArgInfo) -> Mode:
  match value:
    case SNil{}: Fetch{state, info}
    case _: scan_settle(scan_value(state, info, value))

def scan_short_value(chars: String, state: ScanState,
    info: ArgInfo) -> Mode:
  scan_short_value_attached(short_attached(chars), state, info)

def scan_short_bare_value(chars: String, state: ScanState,
    +info: ArgInfo) -> Mode:
  match chars:
    case SNil{}:
      scan_settle(scan_value(state, info, info_bare_value(info)))
    case _:
      scan_settle(scan_value(state, info, short_attached(chars)))

def scan_short_go(chars: String, +state: ScanState,
    found: Maybe<&2, OptFound>) -> Mode:
  match chars found:
    case SNil{} _:
      scan_settle(state)
    case SCon{Chr{104}, +tail} None{}:
      Closed{Stopped{scan_event(state, HelpHit{False{}})}}
    case SCon{Chr{86}, tail} None{}:
      +enabled = scope_version(scan_state_scope(state))
      +next = scan_event(state, VersionHit{})
      Bool.pick(Mode, enabled,
        Closed{Stopped{next}},
        scan_settle(scan_error(state, E01{"-V"})))
    case SCon{head, tail} None{}:
      scan_settle(scan_error(state,
        E01{String.append("-", Char.show(head))}))
    case SCon{head, tail} Some{OptFound{arg, polarity}}:
      match arg:
        case ArgInfo{id, usage, short, long, kind, attrs}:
          match kind:
            case FlagKind{}:
              +next = scan_event(state, FlagHit{id, polarity})
              scan_short_go(tail, next, find_short_for_head(tail, next))
            case CountKind{}:
              +next = scan_event(state, CountHit{id})
              scan_short_go(tail, next, find_short_for_head(tail, next))
            case NegatableKind{}:
              +next = scan_event(state, FlagHit{id, polarity})
              scan_short_go(tail, next, find_short_for_head(tail, next))
            case OptionKind{many}:
              scan_short_value(tail, state,
                ArgInfo{id, usage, short, long, OptionKind{many}, attrs})
            case BareOptionKind{}:
              scan_short_bare_value(tail, state,
                ArgInfo{id, usage, short, long, BareOptionKind{}, attrs})
            case PosKind{required, many}:
              scan_settle(state)

def scan_short(token: String, +state: ScanState) -> Mode:
  +chars = String.drop(token, 1n)
  scan_short_go(chars, state, find_short_for_head(chars, state))

def scope_items(scope: Scope) -> List<&2, Item>:
  match scope:
    case Scope{path, items, globals}: items

def scan_sub_unknown(allow_external: Bool, state: ScanState,
    token: String) -> Mode:
  match allow_external:
    case True{}: Capture{state, token}
    case False{}: Closed{Stopped{scan_error(state, E02{token})}}

def scan_sub_found(found: Maybe<&2, SubFound>, +state: ScanState,
    token: String) -> Mode:
  match found:
    case Some{sub}: scan_settle(scan_descend(state, sub))
    case None{}:
      scan_sub_unknown(has_external(scope_items(scan_state_scope(state))),
        state, token)

def help_missing(+token: String, +state: ScanState) -> Tail:
  Bool.pick(Tail, String.eq(token, "-h"),
    Stopped{scan_event(state, HelpHit{False{}})},
    Bool.pick(Tail, String.eq(token, "--help"),
      Stopped{scan_event(state, HelpHit{True{}})},
      Bool.pick(Tail, String.starts_with(token, "-"),
        Stopped{scan_error(state, E01{token})},
        Stopped{scan_error(state, E02{token})})))

def help_walk(found: Maybe<&2, SubFound>, state: ScanState,
    token: String) -> Tail:
  match found:
    case Some{sub}: Walk{scan_descend(state, sub)}
    case None{}: help_missing(token, state)

def scan_non_option_sub(+token: String, +state: ScanState) -> Mode:
  Bool.pick(Mode, String.eq(token, "help"),
    Closed{Walk{state}},
    scan_sub_found(find_sub(scope_items(scan_state_scope(state)), token),
      state, token))

def scan_non_option(+token: String, +state: ScanState) -> Mode:
  Bool.pick(Mode,
    has_sub_item(scope_items(scan_state_scope(state))),
    scan_non_option_sub(token, state),
    scan_settle(scan_operand(state, token)))

def scan_hyphen_candidate(state: ScanState, +token: String) -> Bool:
  match state:
    case ScanState{+scope, events, resting, positional_count,
        external, issue}:
      +slot = scope_next_slot(scope, positional_count)
      Bool.or(Bool.and(slot_hyphen(slot),
        Bool.not(scope_any_option_known(scope, token))),
        Bool.and(slot_f32(slot),
          Bool.and(is_negative_number(token),
            Bool.not(scope_digit_short(scope)))))

def scan_dash_token(+token: String, +state: ScanState) -> Mode:
  Bool.pick(Mode, scan_hyphen_candidate(state, token),
    scan_settle(scan_operand(state, token)),
    scan_short(token, state))

def scan_token(+token: String, +state: ScanState) -> Mode:
  Bool.pick(Mode, String.starts_with(token, "--"),
    scan_long(token, state),
    Bool.pick(Mode,
      Bool.and(String.starts_with(token, "-"),
        Bool.not(String.eq(token, "-"))),
      scan_dash_token(token, state),
      scan_non_option(token, state)))

def scan_tail(tail: Tail, +token: String) -> Tail:
  match tail:
    case Faulted{state}: scan_faulted(state, token)
    case Walk{+state}:
      help_walk(find_sub(scope_items(scan_state_scope(state)), token),
        state, token)
    case Stopped{state}: Stopped{state}

# `--` ends options only here, while the scan is open (R1).
def scan_open(dash: Bool, state: ScanState, token: String) -> Mode:
  match dash:
    case True{}: Operands{state, True{}}
    case False{}: scan_token(token, state)

# An external subcommand takes the rest of argv verbatim.
def scan_go(tokens: List<&2, String>, mode: Mode) -> Mode:
  match tokens mode:
    case argv Capture{state, name}:
      Closed{Stopped{scan_external(state, name, argv)}}
    case Nil{} _: mode
    case +token <> rest Open{state}:
      scan_go(rest, scan_open(String.eq(token, "--"), state, token))
    case token <> rest Fetch{state, info}:
      scan_go(rest, scan_fetch(state, info, token))
    case token <> rest Operands{state, ended}:
      scan_go(rest, Operands{scan_operand(state, token), ended})
    case token <> rest Closed{tail}:
      scan_go(rest, Closed{scan_tail(tail, token)})

def scan_tail_close(tail: Tail) -> ScanState:
  match tail:
    case Faulted{state}: state
    case Walk{state}: scan_event(state, HelpHit{True{}})
    case Stopped{state}: state

def scan_close(mode: Mode) -> ScanState:
  match mode:
    case Open{state}: state
    case Fetch{state, info}: scan_error(state, E03{arg_display(info)})
    case Operands{state, ended}: state
    case Capture{state, name}: scan_external(state, name, [])
    case Closed{tail}: scan_tail_close(tail)

def scan_trace_of(state: ScanState, ended: Bool) -> ScanTrace:
  match state:
    case ScanState{scope, events, resting, positional_count,
        external, issue}:
      match scope:
        case Scope{path, items, globals}:
          ScanTrace{path, List.reverse(&2, ScanEvent, events),
            ended, external, issue}

def scan_trace(mode: Mode) -> ScanTrace:
  match mode:
    case Operands{state, ended}: scan_trace_of(state, ended)
    case other: scan_trace_of(scan_close(other), False{})

def scan(c: Cmd, argv: List<&2, String>) -> ScanTrace:
  scan_trace(scan_go(argv, Open{scan_start(c)}))

def find_early(events: List<&2, ScanEvent>) -> Maybe<&2, Early>:
  match events:
    case Nil{}: None{}
    case HelpHit{long} <> tail: Some{EarlyHelp{long}}
    case VersionHit{} <> tail: Some{EarlyVersion{}}
    case event <> tail: find_early(tail)

def scope_path(scope: Scope) -> List<&2, String>:
  match scope:
    case Scope{path, items, globals}: path

# A command that cannot complete without a subcommand (§8.4).
def needs_sub(+items: List<&2, Item>) -> Bool:
  Bool.and(has_sub_item(items),
    Bool.and(Bool.not(has_sub_optional(items)),
      Bool.not(has_external(items))))

def scope_needs_sub(scope: Scope) -> Bool:
  match scope:
    case Scope{path, items, globals}: needs_sub(items)

def bool_text(value: Bool) -> String:
  Bool.pick(String, value, "true", "false")

def gather_value(gather: Gather, +value: String,
    many: Bool) -> Gather:
  match gather:
    case Gather{seen, values, +count}:
      Bool.pick(Gather, many,
        Gather{True{}, List.append(&2, String, values, [value]), count},
        Gather{True{}, [value], count})

def gather_flag(gather: Gather, value: Bool) -> Gather:
  match gather:
    case Gather{seen, values, count}:
      Gather{True{}, [bool_text(value)], count}

def gather_count(gather: Gather) -> Gather:
  match gather:
    case Gather{seen, values, count}:
      +next = Nat.add(count, 1n)
      Gather{True{}, [Nat.show(next)], next}

def kind_many(kind: UsageKind) -> Bool:
  match kind:
    case OptionKind{many}: many
    case PosKind{required, many}: many
    case _: False{}

def gather_event(event: ScanEvent, id: String,
    kind: UsageKind, +gather: Gather) -> Gather:
  match event:
    case ValueHit{key, value}:
      Bool.pick(Gather, String.eq(key, id),
        gather_value(gather, value, kind_many(kind)), gather)
    case FlagHit{key, value}:
      Bool.pick(Gather, String.eq(key, id),
        gather_flag(gather, value), gather)
    case CountHit{key}:
      Bool.pick(Gather, String.eq(key, id),
        gather_count(gather), gather)
    case _: gather

def gather_events(events: List<&2, ScanEvent>, +id: String,
    +kind: UsageKind, gather: Gather) -> Gather:
  match events:
    case Nil{}: gather
    case event <> tail:
      gather_events(tail, id, kind,
        gather_event(event, id, kind, gather))

def gather_arg(events: List<&2, ScanEvent>, info: ArgInfo) -> Gather:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}:
      gather_events(events, id, kind, Gather{False{}, [], 0n})

def find_env(attrs: List<&2, Item>) -> Maybe<&2, String>:
  match attrs:
    case Nil{}: None{}
    case AttrEnv{name} <> tail: Some{name}
    case head <> tail: find_env(tail)

def env_present(name: String, found: Maybe<&2, String>) ->
    Maybe<&2, EnvValue>:
  match found:
    case None{}: None{}
    case Some{+value}:
      Bool.pick(Maybe<&2, EnvValue>, String.is_empty(value),
        None{}, Some{EnvValue{name, value}})

def host_env(found: Maybe<&2, String>, h: Host) ->
    Maybe<&2, EnvValue>:
  match found:
    case None{}: None{}
    case Some{+name}:
      env_present(name, host_value(h, name))

def env_bool_true(value: String) -> Bool:
  List.contains(~String, ~String.eq,
    ["true", "yes", "on", "1"], String.to_lower(value))

def env_values(kind: UsageKind, attrs: List<&2, Item>,
    value: String) -> List<&2, String>:
  match kind:
    case FlagKind{}: [bool_text(env_bool_true(value))]
    case NegatableKind{}: [bool_text(env_bool_true(value))]
    case CountKind{}: [value]
    case _: apply_delim(find_delim(attrs), [value])

def resolve_env_valid(found: Maybe<&2, Bad>, info: ArgInfo,
    name: String, value: String) -> FieldBuild:
  match found:
    case Some{Bad{bad, why}}:
      BuildFault{E11{arg_display(info), bad, name, why}}
    case None{}:
      match info:
        case ArgInfo{id, usage, short, long, kind, attrs}:
          Built{[Field{id, env_values(kind, attrs, value), Env{}}]}

def resolve_env(+info: ArgInfo, env: EnvValue) -> FieldBuild:
  match env:
    case EnvValue{name, +value}:
      resolve_env_valid(value_issue(info_kind(info), info_attrs(info), value),
        info, name, value)

def resolve_default(found: Maybe<&2, String>,
    info: ArgInfo) -> FieldBuild:
  match found:
    case None{}: Built{[]}
    case Some{value}:
      match info:
        case ArgInfo{id, usage, short, long, kind, attrs}:
          Built{[Field{id, env_values(kind, attrs, value), Default{}}]}

def info_default(info: ArgInfo) -> Maybe<&2, String>:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}:
      find_default(attrs)

def resolve_env_default(found: Maybe<&2, EnvValue>,
    +info: ArgInfo) -> FieldBuild:
  match found:
    case Some{env}: resolve_env(info, env)
    case None{}: resolve_default(info_default(info), info)

def info_env(info: ArgInfo) -> Maybe<&2, String>:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}:
      find_env(attrs)

def resolve_argv_gather(gather: Gather, +info: ArgInfo,
    h: Host) -> FieldBuild:
  match gather:
    case Gather{True{}, values, count}:
      match info:
        case ArgInfo{id, usage, short, long, kind, attrs}:
          Built{[Field{id, apply_delim(find_delim(attrs), values),
            Argv{}}]}
    case Gather{False{}, values, count}:
      resolve_env_default(host_env(info_env(info), h), info)

def resolve_option(+info: ArgInfo,
    events: List<&2, ScanEvent>, h: Host) -> FieldBuild:
  resolve_argv_gather(gather_arg(events, info), info, h)

def scope_arg_items(scope: Scope) -> List<&2, Item>:
  match scope:
    case Scope{path, items, globals}:
      List.append(&2, Item, globals, items)

def combine_built(fields: List<&2, Field>,
    next: FieldBuild) -> FieldBuild:
  match next:
    case Built{more}:
      Built{List.append(&2, Field, fields, more)}
    case BuildFault{fault}: BuildFault{fault}

def combine_build(first: FieldBuild,
    second: FieldBuild) -> FieldBuild:
  match first:
    case Built{fields}: combine_built(fields, second)
    case BuildFault{fault}: BuildFault{fault}

def resolve_options(items: List<&2, Item>,
    +events: List<&2, ScanEvent>, +h: Host) -> FieldBuild:
  match items:
    case Nil{}: Built{[]}
    case Arg{+usage, help, attrs} <> tail:
      +later = resolve_options(tail, events, h)
      Bool.pick(FieldBuild,
        usage_kind(~kind_pos, parse_usage(usage)), later,
        combine_build(resolve_option(arg_info(usage, attrs), events, h),
          later))
    case head <> tail: resolve_options(tail, events, h)

def scan_operands(events: List<&2, ScanEvent>) ->
    List<&2, String>:
  match events:
    case Nil{}: Nil{}
    case Operand{token} <> tail:
      token <> scan_operands(tail)
    case event <> tail: scan_operands(tail)

def position_take_count(kind: UsageKind,
    after: List<&2, Item>, +tokens: List<&2, String>) -> Nat:
  match kind:
    case PosKind{required, True{}}:
      Nat.sub(List.length(&2, String, tokens),
        List.length(&2, Item, after))
    case _:
      Bool.pick(Nat, List.is_empty(&2, String, tokens), 0n, 1n)

def pos_valid_result(found: Maybe<&2, Bad>,
    info: ArgInfo, values: List<&2, String>) -> FieldBuild:
  match found:
    case Some{Bad{bad, why}}:
      BuildFault{E04{arg_display(info), bad, why}}
    case None{}:
      match info:
        case ArgInfo{id, usage, short, long, kind, attrs}:
          Built{[Field{id, values, Argv{}}]}

def resolve_pos(+info: ArgInfo,
    +values: List<&2, String>, h: Host) -> FieldBuild:
  match values:
    case Nil{}:
      resolve_env_default(host_env(info_env(info), h), info)
    case head <> tail:
      +attrs = info_attrs(info)
      +split = apply_delim(find_delim(attrs), values)
      pos_valid_result(first_bad(split, attrs), info, split)

def resolve_positions(slots: List<&2, Item>,
    +tokens: List<&2, String>, +h: Host) -> FieldBuild:
  match slots:
    case Nil{}: Built{[]}
    case Arg{usage, help, attrs} <> +tail:
      +info = arg_info(usage, attrs)
      +amount = position_take_count(info_kind(info), tail, tokens)
      combine_build(
        resolve_pos(info, List.take(&2, String, tokens, amount), h),
        resolve_positions(tail, List.drop(&2, String, tokens, amount), h))
    case head <> tail: resolve_positions(tail, tokens, h)

def scope_positions(scope: Scope) -> List<&2, Item>:
  match scope:
    case Scope{path, items, globals}:
      positional_items(items)

def resolve_scope(+scope: Scope, +events: List<&2, ScanEvent>,
    +h: Host) -> FieldBuild:
  combine_build(
    resolve_options(scope_arg_items(scope), events, h),
    resolve_positions(scope_positions(scope),
      scan_operands(events), h))

def source_given(source: Src) -> Bool:
  match source:
    case Argv{}: True{}
    case Env{}: True{}
    case Default{}: False{}
    case Absent{}: False{}

def field_source(fields: List<&2, Field>, +id: String) -> Src:
  match fields:
    case Nil{}: Absent{}
    case Field{key, values, source} <> tail:
      Bool.pick(Src, String.eq(key, id), source,
        field_source(tail, id))

def field_given(fields: List<&2, Field>, id: String) -> Bool:
  source_given(field_source(fields, id))

def source_present(source: Src) -> Bool:
  match source:
    case Absent{}: False{}
    case _: True{}

def field_present(fields: List<&2, Field>, id: String) -> Bool:
  source_present(field_source(fields, id))

def arg_in_group(attrs: List<&2, Item>, name: String) -> Bool:
  List.contains(~String, ~String.eq,
    find_group_attrs(attrs), name)

def group_usages(items: List<&2, Item>, +name: String) ->
    List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Arg{+usage, help, +attrs} <> tail:
      +later = group_usages(tail, name)
      Bool.pick(List<&2, String>, arg_in_group(attrs, name),
        arg_display(arg_info(usage, attrs)) <> later, later)
    case head <> tail: group_usages(tail, name)

def info_id(info: ArgInfo) -> String:
  match info:
    case ArgInfo{id, usage, short, long, kind, attrs}: id

def group_given(items: List<&2, Item>,
    +fields: List<&2, Field>, +name: String) -> Bool:
  match items:
    case Nil{}: False{}
    case Arg{usage, help, +attrs} <> tail:
      Bool.or(Bool.and(arg_in_group(attrs, name),
        field_given(fields, info_id(arg_info(usage, attrs)))),
        group_given(tail, fields, name))
    case head <> tail: group_given(tail, fields, name)

def arg_required_missing(info: ArgInfo,
    +fields: List<&2, Field>) -> Bool:
  match info:
    case ArgInfo{+id, usage, short, long, kind, attrs}:
      Bool.or(Bool.and(has_required(attrs),
        Bool.not(field_given(fields, id))),
        Bool.and(kind_required_pos(kind),
          Bool.not(field_present(fields, id))))

def group_display(items: List<&2, Item>, name: String) -> String:
  String.concat(["<", String.join(group_usages(items, name), "|"), ">"])

def missing_arg(+info: ArgInfo,
    fields: List<&2, Field>) -> List<&2, String>:
  Bool.pick(List<&2, String>,
    arg_required_missing(info, fields),
    [arg_display(info)], [])

def missing_group(+items: List<&2, Item>,
    fields: List<&2, Field>, +name: String) -> List<&2, String>:
  Bool.pick(List<&2, String>,
    group_given(items, fields, name), [],
    [group_display(items, name)])

def missing_items(items: List<&2, Item>,
    +all_items: List<&2, Item>,
    +fields: List<&2, Field>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Arg{usage, help, attrs} <> tail:
      List.append(&2, String,
        missing_arg(arg_info(usage, attrs), fields),
        missing_items(tail, all_items, fields))
    case NeedOne{name} <> tail:
      List.append(&2, String,
        missing_group(all_items, fields, name),
        missing_items(tail, all_items, fields))
    case head <> tail:
      missing_items(tail, all_items, fields)

def scope_missing(scope: Scope,
    fields: List<&2, Field>) -> List<&2, String>:
  +items = scope_arg_items(scope)
  missing_items(items, items, fields)

def event_id(event: ScanEvent) -> Maybe<&2, String>:
  match event:
    case FlagHit{id, value}: Some{id}
    case CountHit{id}: Some{id}
    case ValueHit{id, value}: Some{id}
    case _: None{}

def append_unique(+ids: List<&2, String>, +id: String) ->
    List<&2, String>:
  Bool.pick(List<&2, String>,
    List.contains(~String, ~String.eq, ids, id), ids,
    List.append(&2, String, ids, [id]))

def append_event_id(found: Maybe<&2, String>,
    ids: List<&2, String>) -> List<&2, String>:
  match found:
    case None{}: ids
    case Some{id}: append_unique(ids, id)

def argv_order(events: List<&2, ScanEvent>,
    ids: List<&2, String>) -> List<&2, String>:
  match events:
    case Nil{}: ids
    case event <> tail:
      argv_order(tail, append_event_id(event_id(event), ids))

def source_env(source: Src) -> Bool:
  match source:
    case Env{}: True{}
    case _: False{}

def env_order(fields: List<&2, Field>,
    +ids: List<&2, String>) -> List<&2, String>:
  match fields:
    case Nil{}: ids
    case Field{id, values, source} <> tail:
      env_order(tail, Bool.pick(List<&2, String>,
        source_env(source), append_unique(ids, id), ids))

def present_order(events: List<&2, ScanEvent>,
    fields: List<&2, Field>) -> List<&2, String>:
  env_order(fields, argv_order(events, []))

def find_arg_info(items: List<&2, Item>, +id: String) ->
    Maybe<&2, ArgInfo>:
  match items:
    case Nil{}: None{}
    case Arg{usage, help, attrs} <> tail:
      +info = arg_info(usage, attrs)
      Bool.pick(Maybe<&2, ArgInfo>, String.eq(info_id(info), id),
        Some{info}, find_arg_info(tail, id))
    case head <> tail: find_arg_info(tail, id)

def exclusive_groups(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Exclusive{name} <> tail:
      name <> exclusive_groups(tail)
    case head <> tail: exclusive_groups(tail)

def common_exclusive(groups: List<&2, String>,
    +left: List<&2, String>, +right: List<&2, String>) -> Bool:
  match groups:
    case Nil{}: False{}
    case +name <> tail:
      Bool.or(Bool.and(
        List.contains(~String, ~String.eq, left, name),
        List.contains(~String, ~String.eq, right, name)),
        common_exclusive(tail, left, right))

def pair_conflicts(+later: ArgInfo, +earlier: ArgInfo,
    groups: List<&2, String>) -> Bool:
  +later_attrs = info_attrs(later)
  +earlier_attrs = info_attrs(earlier)
  Bool.or(List.contains(~String, ~String.eq,
      find_conflicts(later_attrs), info_id(earlier)),
    Bool.or(List.contains(~String, ~String.eq,
        find_conflicts(earlier_attrs), info_id(later)),
      common_exclusive(groups,
        find_group_attrs(later_attrs),
        find_group_attrs(earlier_attrs))))

def pair_fault(+later: ArgInfo, earlier: Maybe<&2, ArgInfo>,
    groups: List<&2, String>) -> Maybe<&2, ScanFault>:
  match earlier:
    case None{}: None{}
    case Some{+prior}:
      Bool.pick(Maybe<&2, ScanFault>,
        pair_conflicts(later, prior, groups),
        Some{E07{arg_display(later), arg_display(prior)}}, None{})

def earlier_conflict(earlier_ids: List<&2, String>,
    +later: ArgInfo, +items: List<&2, Item>,
    +groups: List<&2, String>,
    found: Maybe<&2, ScanFault>) -> Maybe<&2, ScanFault>:
  match earlier_ids found:
    case Nil{} Some{fault}: Some{fault}
    case Nil{} None{}: None{}
    case id <> tail Some{fault}: Some{fault}
    case id <> tail None{}:
      earlier_conflict(tail, later, items, groups,
        pair_fault(later, find_arg_info(items, id), groups))

def conflict_for_id(info: Maybe<&2, ArgInfo>,
    seen: List<&2, String>, items: List<&2, Item>,
    groups: List<&2, String>) -> Maybe<&2, ScanFault>:
  match info:
    case None{}: None{}
    case Some{later}:
      earlier_conflict(seen, later, items, groups, None{})

def conflict_go(ids: List<&2, String>,
    +seen: List<&2, String>, +items: List<&2, Item>,
    +groups: List<&2, String>,
    found: Maybe<&2, ScanFault>) -> Maybe<&2, ScanFault>:
  match ids found:
    case Nil{} Some{fault}: Some{fault}
    case Nil{} None{}: None{}
    case id <> tail Some{fault}: Some{fault}
    case +id <> tail None{}:
      conflict_go(tail, List.append(&2, String, seen, [id]),
        items, groups,
        conflict_for_id(find_arg_info(items, id),
          seen, items, groups))

def require_target_fault(target: Maybe<&2, ArgInfo>,
    +requester: ArgInfo, fields: List<&2, Field>) ->
    Maybe<&2, ScanFault>:
  match target:
    case None{}: None{}
    case Some{+needed}:
      Bool.pick(Maybe<&2, ScanFault>,
        Bool.not(field_given(fields, info_id(needed))),
        Some{E08{arg_display(requester), arg_display(needed)}},
        None{})

def require_targets(targets: List<&2, String>,
    +requester: ArgInfo, +items: List<&2, Item>,
    +fields: List<&2, Field>,
    found: Maybe<&2, ScanFault>) -> Maybe<&2, ScanFault>:
  match targets found:
    case Nil{} Some{fault}: Some{fault}
    case Nil{} None{}: None{}
    case name <> tail Some{fault}: Some{fault}
    case name <> tail None{}:
      require_targets(tail, requester, items, fields,
        require_target_fault(find_arg_info(items, name),
          requester, fields))

def require_for_id(info: Maybe<&2, ArgInfo>,
    items: List<&2, Item>,
    fields: List<&2, Field>) -> Maybe<&2, ScanFault>:
  match info:
    case None{}: None{}
    case Some{+requester}:
      require_targets(find_requires(info_attrs(requester)),
        requester, items, fields, None{})

def require_go(ids: List<&2, String>,
    +items: List<&2, Item>, +fields: List<&2, Field>,
    found: Maybe<&2, ScanFault>) -> Maybe<&2, ScanFault>:
  match ids found:
    case Nil{} Some{fault}: Some{fault}
    case Nil{} None{}: None{}
    case id <> tail Some{fault}: Some{fault}
    case id <> tail None{}:
      require_go(tail, items, fields,
        require_for_id(find_arg_info(items, id), items, fields))

def parse_requires(fault: Maybe<&2, ScanFault>,
    path: List<&2, String>, fields: List<&2, Field>,
    external: Maybe<&2, ExternalArgs>) -> ParseResult:
  match fault:
    case Some{problem}: Rejected{path, problem}
    case None{}: Accepted{path, fields, external}

def parse_conflicts(fault: Maybe<&2, ScanFault>,
    +scope: Scope, +fields: List<&2, Field>,
    events: List<&2, ScanEvent>,
    external: Maybe<&2, ExternalArgs>) -> ParseResult:
  match fault:
    case Some{problem}: Rejected{scope_path(scope), problem}
    case None{}:
      parse_requires(require_go(
          present_order(events, fields),
          scope_arg_items(scope), fields, None{}),
        scope_path(scope), fields, external)

def parse_missing(missing: List<&2, String>,
    +scope: Scope, +fields: List<&2, Field>,
    +events: List<&2, ScanEvent>,
    empty: Bool, external: Maybe<&2, ExternalArgs>) -> ParseResult:
  match missing:
    case Nil{}:
      +items = scope_arg_items(scope)
      parse_conflicts(conflict_go(present_order(events, fields),
          [], items, exclusive_groups(items), None{}),
        scope, fields, events, external)
    case head <> tail:
      Bool.pick(ParseResult, empty, SummaryRequired{},
        Rejected{scope_path(scope), E06{head <> tail}})

def parse_built(build: FieldBuild, +scope: Scope,
    events: List<&2, ScanEvent>, empty: Bool,
    external: Maybe<&2, ExternalArgs>) -> ParseResult:
  match build:
    case BuildFault{fault}: Rejected{scope_path(scope), fault}
    case Built{+fields}:
      parse_missing(scope_missing(scope, fields),
        scope, fields, events, empty, external)

def parse_no_issue(needs_sub: Bool, +scope: Scope,
    +events: List<&2, ScanEvent>, +h: Host,
    +empty: Bool, external: Maybe<&2, ExternalArgs>) -> ParseResult:
  Bool.pick(ParseResult, needs_sub,
    Bool.pick(ParseResult, empty, SummaryRequired{},
      Rejected{scope_path(scope), E10{}}),
    parse_built(resolve_scope(scope, events, h),
      scope, events, empty, external))

def parse_issue(issue: Maybe<&2, ScanFault>,
    +scope: Scope, events: List<&2, ScanEvent>,
    h: Host, empty: Bool,
    external: Maybe<&2, ExternalArgs>) -> ParseResult:
  match issue:
    case Some{fault}: Rejected{scope_path(scope), fault}
    case None{}:
      parse_no_issue(scope_needs_sub(scope), scope,
        events, h, empty, external)

def parse_early(found: Maybe<&2, Early>,
    +scope: Scope, events: List<&2, ScanEvent>, h: Host,
    empty: Bool, issue: Maybe<&2, ScanFault>,
    external: Maybe<&2, ExternalArgs>) -> ParseResult:
  match found:
    case Some{EarlyHelp{long}}:
      HelpRequested{scope_path(scope), long}
    case Some{EarlyVersion{}}:
      VersionRequested{}
    case None{}:
      parse_issue(issue, scope, events, h, empty, external)

def parse_from_state(state: ScanState, h: Host,
    empty: Bool) -> ParseResult:
  match state:
    case ScanState{scope, events, resting, positional_count,
        external, issue}:
      +ordered: List<&2, ScanEvent> =
        List.reverse(&2, ScanEvent, events)
      parse_early(find_early(ordered), scope, ordered, h,
        empty, issue, external)

def parse(c: Cmd, h: Host, +argv: List<&2, String>) -> ParseResult:
  parse_from_state(scan_close(scan_go(argv, Open{scan_start(c)})),
    h, List.is_empty(&2, String, argv))

# ---- Reading values (§6.5) ----

type Fault is Data:
  Bug{msg: String}
  Usage{msg: String}

def Dec(-A: Type) -> Type:
  Result<&2, &1, Fault, A>

def Dec.pure(-A: Type, x: A) -> Dec(A):
  Done{x}

def Dec.bind(-A: Type, -B: Type, r: Dec(A), f: A -> Dec(B)) -> Dec(B):
  match r:
    case Fail{e}: Fail{e}
    case Done{x}: f(x)

type Matches is Data:
  Matches{cmd: Cmd, path: List<&2, String>, fields: List<&2, Field>,
    external: Maybe<&2, ExternalArgs>}

def matches(c: Cmd, r: ParseResult) -> Maybe<&2, Matches>:
  match r:
    case Accepted{path, fields, external}:
      Some{Matches{c, path, fields, external}}
    case _: None{}

def path(m: Matches) -> List<&2, String>:
  match m:
    case Matches{cmd, path, fields, external}: path

def external_args(m: Matches) -> Maybe<(String & List<&2, String>)>:
  match m:
    case Matches{cmd, path, fields, None{}}: None{}
    case Matches{cmd, path, fields, Some{ExternalArgs{name, args}}}:
      Some{(name, args)}

def fail(-A: Type, msg: String) -> Dec(A):
  Fail{Usage{msg}}

def bug(-A: Type, msg: String) -> Dec(A):
  Fail{Bug{msg}}

def keep(+m: Matches) -> Dec(Matches):
  Done{m}

# A command path as lint writes it: the root name, then each subcommand.
def path_text(name: String, path: List<&2, String>) -> String:
  String.join(name <> path, " ")

def sub_items(found: Maybe<&2, SubFound>) -> List<&2, Item>:
  match found:
    case None{}: Nil{}
    case Some{SubFound{name, items}}: items

# The args in scope at path (§8.1), as parse orders them: globals first.
def scope_args(path: List<&2, String>, +items: List<&2, Item>,
    globals: List<&2, Item>) -> List<&2, Item>:
  match path:
    case Nil{}: List.append(&2, Item, globals, items)
    case name <> tail:
      scope_args(tail, sub_items(find_sub(items, name)),
        List.append(&2, Item, global_items(items), globals))

type Form is Data:
  ReadOne{}
  ReadOpt{}
  ReadMany{}

# What a reader asks of an arg; Q-static checks it against the spec.
type Want is Data:
  WFlag{}
  WCount{}
  WValue{stem: String, form: Form}
  WAny{}
  WChoose{opt: Bool, keys: List<&2, String>}

def kind_flag(kind: UsageKind) -> Bool:
  match kind:
    case FlagKind{}: True{}
    case NegatableKind{}: True{}
    case _: False{}

def kind_count(kind: UsageKind) -> Bool:
  match kind:
    case CountKind{}: True{}
    case _: False{}

# The reader name a value type reads with: str, nat, u32, f32 or bool.
def type_stem(found: Maybe<&2, ValueType>) -> String:
  match found:
    case Some{TNat{}}: "nat"
    case Some{TU32{}}: "u32"
    case Some{TF32{}}: "f32"
    case Some{TBool{}}: "bool"
    case _: "str"

def stem_noun(+stem: String) -> String:
  Bool.pick(String, String.eq(stem, "str"), "string", stem)

def stem_article(+stem: String) -> String:
  Bool.pick(String, String.eq(stem, "f32"), "an ", "a ")

def always_present(kind: UsageKind, +attrs: List<&2, Item>) -> Bool:
  Bool.or(has_required(attrs), Bool.or(
    Maybe.is_some(&2, String, find_default(attrs)), kind_required_pos(kind)))

def may_absent(+kind: UsageKind, attrs: List<&2, Item>) -> Bool:
  Bool.and(Bool.not(kind_many(kind)),
    Bool.not(always_present(kind, attrs)))

def kind_text(kind: UsageKind, +stem: String) -> String:
  match kind:
    case FlagKind{}: "a flag"
    case NegatableKind{}: "a flag"
    case CountKind{}: "a count"
    case _:
      Bool.pick(String, kind_many(kind),
        String.concat(["a list of ", stem_noun(stem), " values"]),
        String.concat([stem_article(stem), stem_noun(stem), " value"]))

def fit_name(+kind: UsageKind, attrs: List<&2, Item>,
    +stem: String) -> String:
  match kind:
    case FlagKind{}: "flag"
    case NegatableKind{}: "flag"
    case CountKind{}: "count"
    case _:
      Bool.pick(String, kind_many(kind), String.append(stem, "s"),
        Bool.pick(String, always_present(kind, attrs), stem,
          String.append(stem, "_opt")))

def kind_verdict(fits: Bool, id: String, +kind: UsageKind,
    +attrs: List<&2, Item>) -> Maybe<&2, String>:
  match fits:
    case True{}: None{}
    case False{}:
      +stem = type_stem(find_as(attrs))
      Some{String.concat(["'", id, "' is ", kind_text(kind, stem),
        "; read it with Cli.", fit_name(kind, attrs, stem)])}

def absent_verdict(absent: Bool, id: String,
    reader: String) -> Maybe<&2, String>:
  match absent:
    case True{}:
      Some{String.concat(["'", id, "' may be absent; read it with Cli.",
        reader, "_opt"])}
    case False{}: None{}

def all_in(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}: True{}
    case head <> tail:
      Bool.and(List.contains(~String, ~String.eq, ys, head),
        all_in(tail, ys))

def keys_issue(same: Bool, id: String) -> Maybe<&2, String>:
  match same:
    case True{}: None{}
    case False{}:
      Some{String.concat(["choose table for '", id,
        "' does not match its values"])}

def keys_verdict(found: Maybe<&2, List<&2, String>>,
    +keys: List<&2, String>, id: String) -> Maybe<&2, String>:
  match found:
    case None{}: None{}
    case Some{+values}:
      keys_issue(Bool.and(Bool.not(List.is_empty(&2, String, keys)),
        Bool.and(all_in(keys, values), all_in(values, keys))), id)

def form_fits(form: Form, many: Bool) -> Bool:
  match form:
    case ReadMany{}: many
    case _: Bool.not(many)

def form_one(form: Form) -> Bool:
  match form:
    case ReadOne{}: True{}
    case _: False{}

def value_fits(stem: String, form: Form, +kind: UsageKind,
    attrs: List<&2, Item>) -> Bool:
  Bool.and(kind_valued(kind), Bool.and(
    String.eq(stem, type_stem(find_as(attrs))),
    form_fits(form, kind_many(kind))))

def choose_fits(+kind: UsageKind, attrs: List<&2, Item>) -> Bool:
  Bool.and(kind_valued(kind), Bool.and(Bool.not(kind_many(kind)),
    Maybe.is_some(&2, List<&2, String>, find_one_of(attrs))))

# The first Q-static message for an arg in scope: kind, absence, then keys.
def want_verdict(want: Want, +id: String, +kind: UsageKind,
    +attrs: List<&2, Item>) -> Maybe<&2, String>:
  match want:
    case WFlag{}:
      kind_verdict(kind_flag(kind), id, kind, attrs)
    case WCount{}:
      kind_verdict(kind_count(kind), id, kind, attrs)
    case WValue{+stem, +form}:
      Maybe.or(&2, String,
        kind_verdict(value_fits(stem, form, kind, attrs), id, kind, attrs),
        absent_verdict(Bool.and(form_one(form), may_absent(kind, attrs)),
          id, stem))
    case WAny{}:
      None{}
    case WChoose{opt, keys}:
      Maybe.or(&2, String,
        kind_verdict(choose_fits(kind, attrs), id, kind, attrs),
        Maybe.or(&2, String,
          absent_verdict(Bool.and(Bool.not(opt), may_absent(kind, attrs)),
            id, "choose"),
          keys_verdict(find_one_of(attrs), keys, id)))

def arg_verdict(found: Maybe<&2, ArgInfo>, id: String, name: String,
    path: List<&2, String>, want: Want) -> Maybe<&2, String>:
  match found:
    case None{}:
      Some{String.concat(["'", id, "' is not an argument of '",
        path_text(name, path), "'"])}
    case Some{ArgInfo{key, usage, short, long, kind, attrs}}:
      want_verdict(want, id, kind, attrs)

# Q-static: depends only on the spec, the path, the id and the want.
def verdict(cmd: Cmd, +path: List<&2, String>, +id: String,
    want: Want) -> Maybe<&2, String>:
  match cmd:
    case Cmd{name, about, items}:
      arg_verdict(find_arg_info(scope_args(path, items, []), id), id, name,
        path, want)

# The field for id, or an absent one.
def field_find(fields: List<&2, Field>, +id: String) -> Field:
  match fields:
    case Nil{}: Field{id, [], Absent{}}
    case Field{+key, values, source} <> tail:
      Bool.pick(Field, String.eq(key, id), Field{key, values, source},
        field_find(tail, id))

# Validation first; reading a validated value never fails (§6.5).
def read_check(~T: Data, ~get: Field -> T, verdict: Maybe<&2, String>,
    fields: List<&2, Field>, id: String) -> Dec(T):
  match verdict:
    case None{}: Done{get(field_find(fields, id))}
    case Some{msg}: Fail{Bug{msg}}

def read_with(~T: Data, ~get: Field -> T, want: Want, m: Matches,
    +id: String) -> Dec(T):
  match m:
    case Matches{cmd, path, fields, external}:
      read_check(~T, ~get, verdict(cmd, path, id, want), fields, id)

def get_one(~T: Data, ~conv: String -> T, f: Field) -> T:
  match f:
    case Field{id, head <> tail, source}: conv(head)
    case _: conv("")

def get_opt(~T: Data, ~conv: String -> T, f: Field) -> Maybe<&2, T>:
  match f:
    case Field{id, head <> tail, source}: Some{conv(head)}
    case _: None{}

def convert_all(~T: Data, ~conv: String -> T, values: List<&2, String>) ->
    List<&2, T>:
  match values:
    case Nil{}: Nil{}
    case head <> tail: conv(head) <> convert_all(~T, ~conv, tail)

def get_many(~T: Data, ~conv: String -> T, f: Field) -> List<&2, T>:
  match f:
    case Field{id, values, source}: convert_all(~T, ~conv, values)

def true_of(s: String) -> Bool:
  String.eq(s, "true")

def nat_of(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def u32_of(s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

def f32_of(s: String) -> F32:
  Maybe.default(&2, F32, F32.read(s), 0.0)

def flag(m: Matches, id: String) -> Dec(Bool):
  read_with(~Bool, ~(f => get_one(~Bool, ~true_of, f)), WFlag{}, m, id)

def count(m: Matches, id: String) -> Dec(Nat):
  read_with(~Nat, ~(f => get_one(~Nat, ~nat_of, f)),
    WCount{}, m, id)

def str(m: Matches, id: String) -> Dec(String):
  read_with(~String, ~(f => get_one(~String, ~(s => s), f)),
    WValue{"str", ReadOne{}}, m, id)

def str_opt(m: Matches, id: String) -> Dec(Maybe<&2, String>):
  read_with(~Maybe<&2, String>, ~(f => get_opt(~String, ~(s => s), f)),
    WValue{"str", ReadOpt{}}, m, id)

def strs(m: Matches, id: String) -> Dec(List<&2, String>):
  read_with(~List<&2, String>, ~(f => get_many(~String, ~(s => s), f)),
    WValue{"str", ReadMany{}}, m, id)

def nat(m: Matches, id: String) -> Dec(Nat):
  read_with(~Nat, ~(f => get_one(~Nat, ~nat_of, f)),
    WValue{"nat", ReadOne{}}, m, id)

def nat_opt(m: Matches, id: String) -> Dec(Maybe<&2, Nat>):
  read_with(~Maybe<&2, Nat>, ~(f => get_opt(~Nat, ~nat_of, f)),
    WValue{"nat", ReadOpt{}}, m, id)

def nats(m: Matches, id: String) -> Dec(List<&2, Nat>):
  read_with(~List<&2, Nat>, ~(f => get_many(~Nat, ~nat_of, f)),
    WValue{"nat", ReadMany{}}, m, id)

def u32(m: Matches, id: String) -> Dec(U32):
  read_with(~U32, ~(f => get_one(~U32, ~u32_of, f)),
    WValue{"u32", ReadOne{}}, m, id)

def u32_opt(m: Matches, id: String) -> Dec(Maybe<&2, U32>):
  read_with(~Maybe<&2, U32>, ~(f => get_opt(~U32, ~u32_of, f)),
    WValue{"u32", ReadOpt{}}, m, id)

def u32s(m: Matches, id: String) -> Dec(List<&2, U32>):
  read_with(~List<&2, U32>, ~(f => get_many(~U32, ~u32_of, f)),
    WValue{"u32", ReadMany{}}, m, id)

def f32(m: Matches, id: String) -> Dec(F32):
  read_with(~F32, ~(f => get_one(~F32, ~f32_of, f)),
    WValue{"f32", ReadOne{}}, m, id)

def f32_opt(m: Matches, id: String) -> Dec(Maybe<&2, F32>):
  read_with(~Maybe<&2, F32>, ~(f => get_opt(~F32, ~f32_of, f)),
    WValue{"f32", ReadOpt{}}, m, id)

def f32s(m: Matches, id: String) -> Dec(List<&2, F32>):
  read_with(~List<&2, F32>, ~(f => get_many(~F32, ~f32_of, f)),
    WValue{"f32", ReadMany{}}, m, id)

def bool(m: Matches, id: String) -> Dec(Bool):
  read_with(~Bool, ~(f => get_one(~Bool, ~env_bool_true, f)),
    WValue{"bool", ReadOne{}}, m, id)

def bool_opt(m: Matches, id: String) -> Dec(Maybe<&2, Bool>):
  read_with(~Maybe<&2, Bool>, ~(f => get_opt(~Bool, ~env_bool_true, f)),
    WValue{"bool", ReadOpt{}}, m, id)

def bools(m: Matches, id: String) -> Dec(List<&2, Bool>):
  read_with(~List<&2, Bool>, ~(f => get_many(~Bool, ~env_bool_true, f)),
    WValue{"bool", ReadMany{}}, m, id)

def field_src(f: Field) -> Src:
  match f:
    case Field{id, values, source}: source

def given(m: Matches, id: String) -> Dec(Bool):
  read_with(~Bool, ~(f => source_given(field_src(f))), WAny{}, m, id)

def source(m: Matches, id: String) -> Dec(Src):
  read_with(~Src, ~field_src, WAny{}, m, id)

# The value under the first key equal to key.
def find_by_key(a, -A: Kind(a), keys: List<&2, String>, values: List<a, A>,
    +key: String) -> Maybe<a, A>:
  match keys:
    case Nil{}: None{}
    case head <> tail:
      match values:
        case Nil{}: None{}
        case value <> rest:
          Bool.pick(Maybe<a, A>, String.eq(head, key), Some{value},
            find_by_key(a, A, tail, rest, key))

def keyed_cons(a, -A: Kind(a), key: String, value: A,
    rest: (List<&2, String> & List<a, A>)) -> (List<&2, String> & List<a, A>):
  (keys, values) = rest
  (key <> keys, value <> values)

# A choose or route table as its keys and its values.
def unzip_keyed(a, -A: Kind(a), table: List<(String & A)>) ->
    (List<&2, String> & List<a, A>):
  match table:
    case Nil{}: ([], [])
    case entry <> tail:
      (key, value) = entry
      keyed_cons(a, A, key, value, unzip_keyed(a, A, tail))

# After validation the key exists: parse and samples keep one_of values.
def choice_dec(-A: Data, found: Maybe<&2, A>) -> Dec(Maybe<&2, A>):
  match found:
    case Some{value}: Done{Some{value}}
    case None{}: Fail{Usage{"the value has no choose entry"}}

def choose_read(-A: Data, keys: List<&2, String>, values: List<&2, A>,
    f: Field) -> Dec(Maybe<&2, A>):
  match f:
    case Field{id, head <> tail, source}:
      choice_dec(A, find_by_key(&2, A, keys, values, head))
    case _: Done{None{}}

def choose_check(-A: Data, verdict: Maybe<&2, String>,
    keys: List<&2, String>, values: List<&2, A>,
    fields: List<&2, Field>, id: String) -> Dec(Maybe<&2, A>):
  match verdict:
    case None{}: choose_read(A, keys, values, field_find(fields, id))
    case Some{msg}: Fail{Bug{msg}}

def choose_pick(-A: Data, opt: Bool,
    choices: (List<&2, String> & List<&2, A>), m: Matches,
    +id: String) -> Dec(Maybe<&2, A>):
  (+keys, values) = choices
  match m:
    case Matches{cmd, path, fields, external}:
      choose_check(A, verdict(cmd, path, id, WChoose{opt, keys}),
        keys, values, fields, id)

def choose_opt(-A: Data, m: Matches, id: String,
    table: List<(String & A)>) -> Dec(Maybe<&2, A>):
  choose_pick(A, True{}, unzip_keyed(&2, A, table), m, id)

# After validation a bare choose always has a value.
def choice_must(-A: Data, d: Dec(Maybe<&2, A>)) -> Dec(A):
  match d:
    case Fail{e}: Fail{e}
    case Done{Some{value}}: Done{value}
    case Done{None{}}: Fail{Usage{"the value is absent"}}

def choose(-A: Data, m: Matches, id: String,
    table: List<(String & A)>) -> Dec(A):
  choice_must(A, choose_pick(A, False{}, unzip_keyed(&2, A, table), m, id))

def Call(-A: Type) -> Type:
  @+m: Matches -> Dec(A)

# The declared subcommand name leads to; built-ins are not commands (§6.4).
def sub_children(items: List<&2, Item>, +name: String) ->
    Maybe<&2, List<&2, Item>>:
  match items:
    case Nil{}: None{}
    case Sub{key, about, children} <> tail:
      Bool.pick(Maybe<&2, List<&2, Item>>, String.eq(key, name),
        Some{children}, sub_children(tail, name))
    case head <> tail: sub_children(tail, name)

def user_children(found: Maybe<&2, List<&2, Item>>) ->
    Maybe<&2, List<&2, Item>>:
  match found:
    case None{}: None{}
    case Some{+children}:
      Bool.pick(Maybe<&2, List<&2, Item>>, has_builtin(children), None{},
        Some{children})

def user_sub(items: List<&2, Item>, name: String) ->
    Maybe<&2, List<&2, Item>>:
  user_children(sub_children(items, name))

def is_command(names: List<&2, String>,
    found: Maybe<&2, List<&2, Item>>) -> Bool:
  match names found:
    case Nil{} None{}: False{}
    case Nil{} Some{items}: True{}
    case name <> tail None{}: False{}
    case name <> tail Some{items}: is_command(tail, user_sub(items, name))

# A route key's subcommand names; "" is the root.
def key_names(+key: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.is_empty(key), [], String.split(key, ' '))

def non_command(keys: List<&2, String>, +items: List<&2, Item>) ->
    Maybe<&2, String>:
  match keys:
    case Nil{}: None{}
    case +key <> tail:
      Bool.pick(Maybe<&2, String>, is_command(key_names(key), Some{items}),
        non_command(tail, items), Some{key})

def route_call(-A: Type, bad: Maybe<&2, String>, call: Call(A),
    m: Matches) -> Dec(A):
  match bad:
    case None{}: call(m)
    case Some{key}:
      Fail{Bug{String.concat(["route '", key, "' is not a command"])}}

# No route for the path is checked first, then every key names a command.
def route_found(-A: Type, found: Maybe<Call(A)>, keys: List<&2, String>,
    cmd: Cmd, path: List<&2, String>, m: Matches) -> Dec(A):
  match found cmd:
    case None{} Cmd{name, about, items}:
      Fail{Bug{String.concat(["no route for '", path_text(name, path), "'"])}}
    case Some{call} Cmd{name, about, items}:
      route_call(A, non_command(keys, items), call, m)

def route_pick(-A: Type, routes: (List<&2, String> & List<Call(A)>),
    m: Matches) -> Dec(A):
  (+keys, calls) = routes
  match m:
    case Matches{+cmd, +path, fields, external}:
      route_found(A,
        find_by_key(&1, Call(A), keys, calls, String.join(path, " ")),
        keys, cmd, path, Matches{cmd, path, fields, external})

def route(-A: Type, m: Matches, table: List<(String & Call(A))>) -> Dec(A):
  route_pick(A, unzip_keyed(&1, Call(A), table), m)

# ---- Samples and check (§6.6) ----

def sample_typed(found: Maybe<&2, ValueType>) -> String:
  match found:
    case Some{TNat{}}: "0"
    case Some{TU32{}}: "0"
    case Some{TF32{}}: "0.0"
    case Some{TBool{}}: "false"
    case _: "x"

def sample_choice(found: Maybe<&2, List<&2, String>>,
    attrs: List<&2, Item>) -> String:
  match found:
    case Some{head <> tail}: head
    case _: sample_typed(find_as(attrs))

def sample_value(kind: UsageKind, +attrs: List<&2, Item>) -> String:
  match kind:
    case FlagKind{}: "true"
    case NegatableKind{}: "true"
    case CountKind{}: "1"
    case _: sample_choice(find_one_of(attrs), attrs)

def sample_field(build: FieldBuild, info: ArgInfo) -> List<&2, Field>:
  match build:
    case Built{Nil{}}:
      match info:
        case ArgInfo{id, usage, short, long, kind, attrs}:
          [Field{id, [sample_value(kind, attrs)], Argv{}}]
    case Built{fields}: fields
    case BuildFault{fault}: Nil{}

# Each arg in scope: its default as parse resolves it, else a sample value.
def sample_args(items: List<&2, Item>) -> List<&2, Field>:
  match items:
    case Nil{}: Nil{}
    case Arg{usage, help, attrs} <> tail:
      +info = arg_info(usage, attrs)
      List.append(&2, Field,
        sample_field(resolve_default(info_default(info), info), info),
        sample_args(tail))
    case head <> tail: sample_args(tail)

def sample_fields(c: Cmd, path: List<&2, String>) -> List<&2, Field>:
  match c:
    case Cmd{name, about, items}: sample_args(scope_args(path, items, []))

def sample(+c: Cmd, +path: List<&2, String>) -> Matches:
  Matches{c, path, sample_fields(c, path), None{}}

# The paths below prefix that can complete, in pre-order, without built-ins.
def sub_paths(items: List<&2, Item>, +prefix: List<&2, String>) ->
    List<&2, List<&2, String>>:
  match items:
    case Nil{}: Nil{}
    case Sub{name, about, +children} <> tail:
      +path = List.append(&2, String, prefix, [name])
      List.concat(&2, List<&2, String>, [
        Bool.pick(List<&2, List<&2, String>>,
          Bool.or(has_builtin(children), needs_sub(children)), [], [path]),
        sub_paths(children, path),
        sub_paths(tail, prefix),
      ])
    case head <> tail: sub_paths(tail, prefix)

def sample_paths(c: Cmd) -> List<&2, List<&2, String>>:
  match c:
    case Cmd{name, about, +items}:
      List.append(&2, List<&2, String>,
        Bool.pick(List<&2, List<&2, String>>, needs_sub(items), [], [[]]),
        sub_paths(items, []))

def decode_bug(-A: Type, d: Dec(A), at: String) -> List<&2, Problem>:
  match d:
    case Fail{Bug{msg}}: [DecodeBug{at, msg}]
    case _: Nil{}

def cmd_name(c: Cmd) -> String:
  match c:
    case Cmd{name, about, items}: name

def sample_bugs(~A: Type, ~decode: @+m: Matches -> Dec(A),
    paths: List<&2, List<&2, String>>, +c: Cmd) -> List<&2, Problem>:
  match paths:
    case Nil{}: Nil{}
    case +path <> tail:
      List.append(&2, Problem,
        decode_bug(A, decode(sample(c, path)), path_text(cmd_name(c), path)),
        sample_bugs(~A, ~decode, tail, c))

def check(~A: Type, ~decode: @+m: Matches -> Dec(A), +c: Cmd) ->
    List<&2, Problem>:
  List.append(&2, Problem, problems(c),
    sample_bugs(~A, ~decode, sample_paths(c), c))
# ---- Color (§10.6) ----

type Term is Data:
  Term{out_color: Bool, err_color: Bool, width: Nat}

def host_tty(h: Host, out: Bool, err: Bool) -> Host:
  match h:
    case Host{width, vars, out_tty, err_tty}: Host{width, vars, out, err}

# Rules 1 and 2 apply only to color() exactly as declared.
def color_attrs(attrs: List<&2, Item>) -> Bool:
  match attrs:
    case Con{OneOf{values}, Con{AttrDefault{value}, Con{Global{}, Nil{}}}}:
      Bool.and(String.eq(String.join(values, " "), "auto always never"),
        String.eq(value, "auto"))
    case _: False{}

def is_color(item: Item) -> Bool:
  match item:
    case Arg{usage, help, attrs}:
      Bool.and(String.eq(usage, "--color <WHEN>"),
        Bool.and(String.eq(help, "When to use color"), color_attrs(attrs)))
    case _: False{}

def has_color(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case item <> tail: Bool.or(is_color(item), has_color(tail))

# The pre-scan of argv: the last --color value before `--`, "" for a bare
# --color before a hyphen token.
type Prescan is Data:
  ColorSeek{last: Maybe<&2, String>}
  ColorWant{}
  ColorStop{last: Maybe<&2, String>}

def color_seek(dash: Bool, bare: Bool, attached: Bool, token: String,
    last: Maybe<&2, String>) -> Prescan:
  match dash bare attached:
    case True{} _ _: ColorStop{last}
    case False{} True{} _: ColorWant{}
    case False{} False{} True{}: ColorSeek{Some{String.drop(token, 8n)}}
    case False{} False{} False{}: ColorSeek{last}

def color_want(hyphen: Bool, +token: String) -> Prescan:
  match hyphen:
    case False{}: ColorSeek{Some{token}}
    case True{}:
      color_seek(String.eq(token, "--"), String.eq(token, "--color"),
        String.starts_with(token, "--color="), token, Some{""})

def color_step(state: Prescan, +token: String) -> Prescan:
  match state:
    case ColorSeek{last}:
      color_seek(String.eq(token, "--"), String.eq(token, "--color"),
        String.starts_with(token, "--color="), token, last)
    case ColorWant{}: color_want(String.starts_with(token, "-"), token)
    case ColorStop{last}: ColorStop{last}

def color_scan(argv: List<&2, String>, state: Prescan) -> Prescan:
  match argv:
    case Nil{}: state
    case token <> tail: color_scan(tail, color_step(state, token))

def color_word(always: Bool, never: Bool) -> Maybe<&2, Bool>:
  match always never:
    case True{} _: Some{True{}}
    case False{} True{}: Some{False{}}
    case False{} False{}: None{}

def color_value(found: Maybe<&2, String>) -> Maybe<&2, Bool>:
  match found:
    case None{}: None{}
    case Some{+value}:
      color_word(String.eq(value, "always"), String.eq(value, "never"))

def color_pick(state: Prescan) -> Maybe<&2, Bool>:
  match state:
    case ColorSeek{last}: color_value(last)
    case ColorWant{}: None{}
    case ColorStop{last}: color_value(last)

def color_flag(enabled: Bool, argv: List<&2, String>) -> Maybe<&2, Bool>:
  match enabled:
    case True{}: color_pick(color_scan(argv, ColorSeek{None{}}))
    case False{}: None{}

# An empty variable counts as unset.
def var_set(found: Maybe<&2, String>) -> Bool:
  match found:
    case None{}: False{}
    case Some{value}: Bool.not(String.is_empty(value))

def var_is(found: Maybe<&2, String>, text: String) -> Bool:
  match found:
    case None{}: False{}
    case Some{value}: String.eq(value, text)

def force_set(found: Maybe<&2, String>) -> Bool:
  match found:
    case None{}: False{}
    case Some{+value}:
      Bool.and(Bool.not(String.is_empty(value)),
        Bool.not(String.eq(value, "0")))

def env_off(off: Bool) -> Maybe<&2, Bool>:
  match off:
    case True{}: Some{False{}}
    case False{}: None{}

def env_force(force: Bool, +vars: List<&2, Var>) -> Maybe<&2, Bool>:
  match force:
    case True{}: Some{True{}}
    case False{}:
      env_off(Bool.or(var_is(var_value(vars, "CLICOLOR"), "0"),
        var_is(var_value(vars, "TERM"), "dumb")))

def env_rules(no_color: Bool, +vars: List<&2, Var>) -> Maybe<&2, Bool>:
  match no_color:
    case True{}: Some{False{}}
    case False{}:
      env_force(force_set(var_value(vars, "CLICOLOR_FORCE")), vars)

# Rules 3-6; None leaves rule 7, each stream's TTY.
def env_color(+vars: List<&2, Var>) -> Maybe<&2, Bool>:
  env_rules(var_set(var_value(vars, "NO_COLOR")), vars)

def term_env(found: Maybe<&2, Bool>, out_tty: Bool, err_tty: Bool,
    width: Nat) -> Term:
  match found:
    case Some{+on}: Term{on, on, width}
    case None{}: Term{out_tty, err_tty, width}

def term_for(flag: Maybe<&2, Bool>, vars: List<&2, Var>, out_tty: Bool,
    err_tty: Bool, width: Nat) -> Term:
  match flag:
    case Some{+on}: Term{on, on, width}
    case None{}: term_env(env_color(vars), out_tty, err_tty, width)

def term(c: Cmd, h: Host, argv: List<&2, String>) -> Term:
  match c h:
    case Cmd{name, about, items} Host{width, vars, out_tty, err_tty}:
      term_for(color_flag(has_color(items), argv), vars, out_tty, err_tty,
        width)

# ---- Help (§10.2, §10.3) ----

def plain(text: String) -> Segment:
  Segment{text, []}

def page_width(width: Nat) -> Nat:
  Nat.min(100n, Nat.max(40n, width))

# The first paragraph: the text before the first blank line.
def summary(s: String) -> String:
  match s:
    case SNil{}: SNil{}
    case SCon{Chr{10}, SCon{Chr{10}, tail}}: SNil{}
    case SCon{head, tail}: SCon{head, summary(tail)}

def shown_text(long: Bool, text: String) -> String:
  match long:
    case True{}: text
    case False{}: summary(text)

def filled(s: String) -> Bool:
  Bool.not(String.is_empty(s))

def join_filled(parts: List<&2, String>) -> String:
  String.join(List.filter(~String, ~filled, parts), " ")

# The command at the longest valid prefix of a path, with the globals it
# inherits, root first; stuck once a step names no subcommand.
type View is Data:
  View{path: String, about: String, items: List<&2, Item>,
    globals: List<&2, Item>, root: Bool, stuck: Bool}

def find_command(items: List<&2, Item>, +query: String,
    found: Maybe<&2, Item>) -> Maybe<&2, Item>:
  match items found:
    case _ Some{item}: Some{item}
    case Nil{} None{}: None{}
    case Sub{+name, about, +children} <> tail None{}:
      find_command(tail, query, Bool.pick(Maybe<&2, Item>,
        Bool.or(String.eq(query, name),
          List.contains(~String, ~String.eq, find_aliases(children), query)),
        Some{Sub{name, about, children}}, None{}))
    case head <> tail None{}: find_command(tail, query, None{})

def view_enter(found: Maybe<&2, Item>, path: String, about: String,
    items: List<&2, Item>, globals: List<&2, Item>, root: Bool) -> View:
  match found:
    case Some{Sub{name, sub_about, children}}:
      View{String.concat([path, " ", name]), sub_about, children,
        List.append(&2, Item, globals, global_items(items)), False{}, False{}}
    case _: View{path, about, items, globals, root, True{}}

def view_step(view: View, step: String) -> View:
  match view:
    case View{path, about, items, globals, root, True{}}:
      View{path, about, items, globals, root, True{}}
    case View{path, about, +items, globals, root, False{}}:
      view_enter(find_command(items, step, None{}), path, about, items,
        globals, root)

def view_walk(steps: List<&2, String>, view: View) -> View:
  match steps:
    case Nil{}: view
    case step <> tail: view_walk(tail, view_step(view, step))

def view_of(c: Cmd, path: List<&2, String>) -> View:
  match c:
    case Cmd{name, about, items}:
      view_walk(path, View{name, about, items, [], True{}, False{}})

def arg_pos(usage: String) -> Bool:
  usage_kind(~kind_pos, parse_usage(usage))

def has_plain_option(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Arg{usage, help, +attrs} <> tail:
      Bool.or(Bool.and(Bool.not(arg_pos(usage)),
        Bool.and(Bool.not(has_hidden(attrs)), Bool.not(has_required(attrs)))),
        has_plain_option(tail))
    case head <> tail: has_plain_option(tail)

def required_elem(required: Bool, usage: String, attrs: List<&2, Item>) ->
    List<&2, Segment>:
  match required:
    case True{}: [plain(arg_display(arg_info(usage, attrs)))]
    case False{}: []

def required_options(items: List<&2, Item>) -> List<&2, Segment>:
  match items:
    case Nil{}: Nil{}
    case Arg{+usage, help, +attrs} <> tail:
      List.append(&2, Segment,
        required_elem(Bool.and(Bool.not(arg_pos(usage)), has_required(attrs)),
          usage, attrs),
        required_options(tail))
    case head <> tail: required_options(tail)

def group_elems(items: List<&2, Item>, +args: List<&2, Item>) ->
    List<&2, Segment>:
  match items:
    case Nil{}: Nil{}
    case NeedOne{group} <> tail:
      plain(group_display(args, group)) <> group_elems(tail, args)
    case head <> tail: group_elems(tail, args)

def positional_elems(items: List<&2, Item>) -> List<&2, Segment>:
  match items:
    case Nil{}: Nil{}
    case Arg{+usage, help, attrs} <> tail:
      +rest = positional_elems(tail)
      Bool.pick(List<&2, Segment>, arg_pos(usage), plain(usage) <> rest, rest)
    case head <> tail: positional_elems(tail)

def command_elems(subs: Bool, need: Bool) -> List<&2, Segment>:
  match subs need:
    case False{} _: []
    case True{} True{}: [plain("<COMMAND>")]
    case True{} False{}: [plain("[COMMAND]")]

def options_elem(present: Bool) -> List<&2, Segment>:
  match present:
    case True{}: [plain("[OPTIONS]")]
    case False{}: []

# The path, [OPTIONS], required options, need_one groups as E06 writes them,
# positionals, then the subcommand slot.
def usage_elems(path: String, +items: List<&2, Item>,
    +globals: List<&2, Item>) -> List<&2, Segment>:
  +args = List.append(&2, Item, items, globals)
  List.concat(&2, Segment, [
    [Segment{path, [Bold{}]}],
    options_elem(has_plain_option(args)),
    required_options(args),
    group_elems(items, List.append(&2, Item, globals, items)),
    positional_elems(items),
    command_elems(has_sub_item(items), needs_sub(items)),
  ])

def segment_texts(segs: List<&2, Segment>) -> List<&2, String>:
  match segs:
    case Nil{}: Nil{}
    case Segment{text, styles} <> tail: text <> segment_texts(tail)

def usage_view(view: View) -> String:
  match view:
    case View{path, about, items, globals, root, stuck}:
      String.join(segment_texts(usage_elems(path, items, globals)), " ")

def usage(c: Cmd, path: List<&2, String>) -> String:
  usage_view(view_of(c, path))

# Usage wraps between elements and continues at column 7.
def usage_rest(elems: List<&2, Segment>, +w: Nat, +col: Nat) ->
    List<&2, Segment>:
  match elems:
    case Nil{}: Nil{}
    case Segment{+text, styles} <> tail:
      +ew = width(text)
      +fits = Nat.is_le((col + 1n + ew : Nat), w)
      plain(Bool.pick(String, fits, " ", "\n       ")) <>
        Segment{text, styles} <> usage_rest(tail, w,
          Bool.pick(Nat, fits, (col + 1n + ew : Nat), (7n + ew : Nat)))

def usage_block(elems: List<&2, Segment>, w: Nat) -> List<&2, Segment>:
  match elems:
    case Nil{}: [Segment{"Usage:", [Bold{}, Under{}]}]
    case Segment{+text, styles} <> tail:
      Segment{"Usage:", [Bold{}, Under{}]} <> plain(" ") <>
        Segment{text, styles} <> usage_rest(tail, w, (7n + width(text) : Nat))

# A help row: its left cell, whether it is an option with a short or a
# long-only option, and its right text.
type Row is Data:
  Row{left: List<&2, Segment>, short: Bool, long_only: Bool, right: String}

type Section is Data:
  Section{title: String, rows: List<&2, Row>}

def tag(name: String, values: List<&2, String>) -> String:
  match values:
    case Nil{}: ""
    case head <> tail:
      String.concat(["[", name, ": ", String.join(head <> tail, ", "), "]"])

def maybe_list(found: Maybe<&2, String>) -> List<&2, String>:
  match found:
    case None{}: Nil{}
    case Some{value}: [value]

def list_or_none(found: Maybe<&2, List<&2, String>>) -> List<&2, String>:
  match found:
    case None{}: Nil{}
    case Some{values}: values

def right_text(long: Bool, help: String, +attrs: List<&2, Item>) -> String:
  join_filled([
    shown_text(long, help),
    tag("env", maybe_list(find_env(attrs))),
    tag("default", maybe_list(find_default(attrs))),
    tag("possible values", list_or_none(find_one_of(attrs))),
    tag("aliases", find_aliases(attrs)),
  ])

def bold_names(names: List<&2, String>, first: Bool) -> List<&2, Segment>:
  match names:
    case Nil{}: Nil{}
    case name <> tail:
      List.append(&2, Segment,
        Bool.pick(List<&2, Segment>, first, [], [plain(", ")]),
        Segment{String.trim_start(name), [Bold{}]} <> bold_names(tail, False{}))

# Where an option's value or repeat starts: " <", "[=", or a final "...".
def value_cut(s: String) -> Nat:
  match s:
    case SNil{}: 0n
    case SCon{Chr{32}, SCon{Chr{60}, tail}}: 0n
    case SCon{Chr{91}, SCon{Chr{61}, tail}}: 0n
    case SCon{Chr{46}, SCon{Chr{46}, SCon{Chr{46}, SNil{}}}}: 0n
    case SCon{head, tail}: 1n+value_cut(tail)

# Option names bold; separators, value and repeat plain.
def option_left(+usage: String) -> List<&2, Segment>:
  +cut = value_cut(usage)
  List.append(&2, Segment,
    bold_names(String.split(String.take(usage, cut), ','), True{}),
    [plain(String.drop(usage, cut))])

def arg_row(parsed: Usage, usage: String, help: String,
    attrs: List<&2, Item>, long: Bool) -> Row:
  match parsed:
    case Parsed{id, +short, name, kind}:
      Row{option_left(usage), filled(short), String.is_empty(short),
        right_text(long, help, attrs)}
    case Invalid{col}:
      Row{[plain(usage)], False{}, False{}, right_text(long, help, attrs)}

def find_heading(attrs: List<&2, Item>) -> String:
  match attrs:
    case Nil{}: ""
    case Heading{title} <> tail: title
    case head <> tail: find_heading(tail)

def option_row(shown: Bool, +usage: String, help: String,
    attrs: List<&2, Item>, long: Bool) -> List<&2, Row>:
  match shown:
    case True{}: [arg_row(parse_usage(usage), usage, help, attrs, long)]
    case False{}: []

# The visible options under a heading, "" for Options.
def option_rows(items: List<&2, Item>, +long: Bool, +heading: String) ->
    List<&2, Row>:
  match items:
    case Nil{}: Nil{}
    case Arg{+usage, help, +attrs} <> tail:
      List.append(&2, Row,
        option_row(Bool.and(Bool.not(arg_pos(usage)),
          Bool.and(Bool.not(has_hidden(attrs)),
            String.eq(find_heading(attrs), heading))),
          usage, help, attrs, long),
        option_rows(tail, long, heading))
    case head <> tail: option_rows(tail, long, heading)

def positional_row(shown: Bool, usage: String, help: String,
    attrs: List<&2, Item>, long: Bool) -> List<&2, Row>:
  match shown:
    case True{}:
      [Row{[plain(usage)], False{}, False{}, right_text(long, help, attrs)}]
    case False{}: []

def positional_rows(items: List<&2, Item>, +long: Bool) -> List<&2, Row>:
  match items:
    case Nil{}: Nil{}
    case Arg{+usage, help, +attrs} <> tail:
      List.append(&2, Row,
        positional_row(Bool.and(arg_pos(usage), Bool.not(has_hidden(attrs))),
          usage, help, attrs, long),
        positional_rows(tail, long))
    case head <> tail: positional_rows(tail, long)

def command_row(hidden: Bool, name: String, about: String,
    children: List<&2, Item>) -> List<&2, Row>:
  match hidden:
    case True{}: []
    case False{}:
      [Row{[Segment{name, [Bold{}]}], False{}, False{},
        join_filled([summary(about), tag("aliases", find_aliases(children))])}]

def command_rows(items: List<&2, Item>) -> List<&2, Row>:
  match items:
    case Nil{}: Nil{}
    case Sub{name, about, +children} <> tail:
      List.append(&2, Row,
        command_row(has_hidden(children), name, about, children),
        command_rows(tail))
    case head <> tail: command_rows(tail)

def help_sub_row(present: Bool) -> List<&2, Row>:
  match present:
    case True{}:
      [Row{[Segment{"help", [Bold{}]}], False{}, False{},
        "Print this message or the help of the given subcommand(s)"}]
    case False{}: []

# A built-in option row, without its short when an app arg took it.
def builtin_row(taken: Bool, short: String, long: String,
    text: String) -> Row:
  match taken:
    case True{}: Row{bold_names([long], True{}), False{}, True{}, text}
    case False{}:
      Row{bold_names([short, long], True{}), True{}, False{}, text}

def help_text(differs: Bool, long: Bool) -> String:
  match differs long:
    case False{} _: "Print help"
    case True{} False{}: "Print help (see more with '--help')"
    case True{} True{}: "Print help (see a summary with '-h')"

def version_row(present: Bool, args: List<&2, Item>) -> List<&2, Row>:
  match present:
    case True{}:
      [builtin_row(Maybe.is_some(&2, OptFound, find_option(args, "-V")),
        "-V", "--version", "Print version")]
    case False{}: []

# Headings of visible args, in order of first use.
def heading_titles(items: List<&2, Item>, +seen: List<&2, String>) ->
    List<&2, String>:
  match items:
    case Nil{}: seen
    case Arg{usage, help, +attrs} <> tail:
      +title = find_heading(attrs)
      heading_titles(tail, Bool.pick(List<&2, String>,
        Bool.or(String.is_empty(title), Bool.or(has_hidden(attrs),
          List.contains(~String, ~String.eq, seen, title))),
        seen, List.append(&2, String, seen, [title])))
    case head <> tail: heading_titles(tail, seen)

def heading_sections(titles: List<&2, String>, +args: List<&2, Item>,
    +long: Bool) -> List<&2, Section>:
  match titles:
    case Nil{}: Nil{}
    case +title <> tail:
      Section{title, option_rows(args, long, title)} <>
        heading_sections(tail, args, long)

# Whether a visible arg's help has more than one paragraph.
def args_paragraphs(items: List<&2, Item>) -> Bool:
  match items:
    case Nil{}: False{}
    case Arg{usage, help, attrs} <> tail:
      Bool.or(Bool.and(Bool.not(has_hidden(attrs)),
        String.contains(help, "\n\n")), args_paragraphs(tail))
    case head <> tail: args_paragraphs(tail)

def indent_cell(indent: Bool, left: List<&2, Segment>) -> List<&2, Segment>:
  match indent:
    case True{}: plain("    ") <> left
    case False{}: left

# A left cell; long-only options indent 4 more on a page with a short.
def row_cell(row: Row, shorted: Bool) -> List<&2, Segment>:
  match row:
    case Row{left, short, long_only, right}:
      indent_cell(Bool.and(long_only, shorted), left)

def cell_width(cell: List<&2, Segment>) -> Nat:
  match cell:
    case Nil{}: 0n
    case Segment{text, styles} <> tail: Nat.add(width(text), cell_width(tail))

def row_short(row: Row) -> Bool:
  match row:
    case Row{left, short, long_only, right}: short

def any_short(rows: List<&2, Row>) -> Bool:
  match rows:
    case Nil{}: False{}
    case row <> tail: Bool.or(row_short(row), any_short(tail))

# L, the widest left cell w with 2 + w + 2 <= K.
def widest(rows: List<&2, Row>, +shorted: Bool, +k: Nat, +best: Nat) -> Nat:
  match rows:
    case Nil{}: best
    case row <> tail:
      +w = cell_width(row_cell(row, shorted))
      widest(tail, shorted, k,
        Bool.pick(Nat, Nat.is_le((w + 4n : Nat), k), Nat.max(w, best), best))

def pad_line(line: String, col: Nat) -> String:
  match line:
    case SNil{}: "\n"
    case SCon{head, tail}:
      String.concat(["\n", String.repeat(" ", col), SCon{head, tail}])

def pad_lines(lines: List<&2, String>, +col: Nat) -> List<&2, Segment>:
  match lines:
    case Nil{}: Nil{}
    case line <> tail: plain(pad_line(line, col)) <> pad_lines(tail, col)

def first_then(lines: List<&2, String>, col: Nat) -> List<&2, Segment>:
  match lines:
    case Nil{}: Nil{}
    case line <> tail: plain(line) <> pad_lines(tail, col)

# A cell that fits takes its text after padding to C; one that does not
# stands alone, its text on the next lines at max(C, 10).
def row_form(fits: Bool, cell: List<&2, Segment>, lw: Nat, right: String,
    w: Nat, +c: Nat) -> List<&2, Segment>:
  match fits:
    case True{}:
      plain("  ") <> List.append(&2, Segment, cell,
        plain(String.repeat(" ", (c - 2n - lw : Nat))) <>
          first_then(String.lines(wrap(right, (w - c : Nat))), c))
    case False{}:
      +col = Nat.max(c, 10n)
      plain("  ") <> List.append(&2, Segment, cell,
        pad_lines(String.lines(wrap(right, (w - col : Nat))), col))

def row_lines(row: Row, shorted: Bool, w: Nat, k: Nat, c: Nat) ->
    List<&2, Segment>:
  match row:
    case Row{left, short, long_only, right}:
      +cell = indent_cell(Bool.and(long_only, shorted), left)
      +lw = cell_width(cell)
      row_form(Nat.is_le((lw + 4n : Nat), k), cell, lw, right, w, c)

def rows_lines(rows: List<&2, Row>, +shorted: Bool, +w: Nat, +k: Nat,
    +c: Nat) -> List<&2, Segment>:
  match rows:
    case Nil{}: Nil{}
    case row <> tail:
      plain("\n") <> List.append(&2, Segment, row_lines(row, shorted, w, k, c),
        rows_lines(tail, shorted, w, k, c))

def section_rows(sections: List<&2, Section>) -> List<&2, Row>:
  match sections:
    case Nil{}: Nil{}
    case Section{title, rows} <> tail:
      List.append(&2, Row, rows, section_rows(tail))

def section_blocks(sections: List<&2, Section>, +shorted: Bool, +w: Nat,
    +k: Nat, +c: Nat) -> List<&2, List<&2, Segment>>:
  match sections:
    case Nil{}: Nil{}
    case Section{title, Nil{}} <> tail: section_blocks(tail, shorted, w, k, c)
    case Section{title, rows} <> tail:
      (Segment{String.append(title, ":"), [Bold{}, Under{}]} <>
        rows_lines(rows, shorted, w, k, c)) <>
        section_blocks(tail, shorted, w, k, c)

# One column for the page: C = L + 4, with K = 2W/5.
def sections_blocks(+sections: List<&2, Section>, +w: Nat) ->
    List<&2, List<&2, Segment>>:
  +rows = section_rows(sections)
  +shorted = any_short(rows)
  +k = Nat.div((2n * w : Nat), 5n)
  section_blocks(sections, shorted, w, k,
    (widest(rows, shorted, k, 0n) + 4n : Nat))

def text_block(text: String, w: Nat) -> List<&2, List<&2, Segment>>:
  match text:
    case SNil{}: Nil{}
    case SCon{head, tail}: [[plain(wrap(SCon{head, tail}, w))]]

def example_lines(items: List<&2, Item>) -> List<&2, Segment>:
  match items:
    case Nil{}: Nil{}
    case Example{line, what} <> tail:
      plain(String.concat(["\n  ", what, ":\n    $ ", line])) <>
        example_lines(tail)
    case head <> tail: example_lines(tail)

def examples_block(lines: List<&2, Segment>) -> List<&2, List<&2, Segment>>:
  match lines:
    case Nil{}: Nil{}
    case head <> tail: [Segment{"Examples:", [Bold{}, Under{}]} <> head <> tail]

def after_texts(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case After{text} <> tail: text <> after_texts(tail)
    case head <> tail: after_texts(tail)

def more_blocks(blocks: List<&2, List<&2, Segment>>) -> List<&2, Segment>:
  match blocks:
    case Nil{}: [plain("\n")]
    case block <> tail:
      plain("\n\n") <> List.append(&2, Segment, block, more_blocks(tail))

# Blocks apart by one blank line; the page ends with a newline.
def join_blocks(blocks: List<&2, List<&2, Segment>>) -> List<&2, Segment>:
  match blocks:
    case Nil{}: Nil{}
    case block <> tail: List.append(&2, Segment, block, more_blocks(tail))

def help_page(view: View, +long: Bool, +w: Nat) -> List<&2, Segment>:
  match view:
    case View{path, +about, +items, +globals, root, stuck}:
      +args = List.append(&2, Item, items, globals)
      join_blocks(List.concat(&2, List<&2, Segment>, [
        text_block(shown_text(long, about), w),
        [usage_block(usage_elems(path, items, globals), w)],
        sections_blocks(List.append(&2, Section, [
          Section{"Commands", List.append(&2, Row, command_rows(items),
            help_sub_row(has_sub_item(items)))},
          Section{"Arguments", positional_rows(items, long)},
          Section{"Options", List.concat(&2, Row, [
            option_rows(args, long, ""),
            [builtin_row(Maybe.is_some(&2, OptFound, find_option(args, "-h")),
              "-h", "--help", help_text(Bool.or(String.contains(about, "\n\n"),
                args_paragraphs(args)), long))],
            version_row(Bool.and(root, has_version_item(items)), args),
          ])},
        ], heading_sections(heading_titles(args, []), args, long)), w),
        examples_block(example_lines(items)),
        text_block(String.join(after_texts(items), "\n\n"), w),
      ]))

def help_out(t: Term, view: View, long: Bool) -> String:
  match t:
    case Term{out_color, err_color, width}:
      emit(out_color, help_page(view, long, page_width(width)))

# The help page for the longest valid prefix of path, in stdout's colors.
def help(+c: Cmd, path: List<&2, String>, long: Bool, h: Host) -> String:
  help_out(term(c, h, []), view_of(c, path), long)

# ---- Suggestions (§10.4) ----

type Scored is Data:
  Scored{dist: Nat, name: String}

def row_zero(b: String, +k: Nat) -> List<&2, Nat>:
  match b:
    case SNil{}: [k]
    case SCon{head, tail}: k <> row_zero(tail, (k + 1n : Nat))

def head_nat(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}: 0n
    case head <> tail: head

def tail_nats(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}: Nil{}
    case head <> tail: tail

def same_char(found: Maybe<&2, Char>, c: Char) -> Bool:
  match found:
    case None{}: False{}
    case Some{d}: Char.is_eq(d, c)

# Row i of optimal string alignment for a[i]: up starts at d[i-1][j-1], up2
# at d[i-2][j-2], and left is d[i][j-1].
def osa_row(bs: String, bp: Maybe<&2, Char>, +a: Char,
    +ap: Maybe<&2, Char>, +up: List<&2, Nat>, +up2: List<&2, Nat>,
    left: Nat) -> List<&2, Nat>:
  match bs:
    case SNil{}: Nil{}
    case SCon{+b, tail}:
      +diag = head_nat(up)
      +rest = tail_nats(up)
      +edit = Nat.min(Nat.min((head_nat(rest) + 1n : Nat), (left + 1n : Nat)),
        Bool.pick(Nat, Char.is_eq(a, b), diag, (diag + 1n : Nat)))
      +best = Bool.pick(Nat, Bool.and(same_char(bp, a), same_char(ap, b)),
        Nat.min(edit, (head_nat(up2) + 1n : Nat)), edit)
      best <> osa_row(tail, Some{b}, a, ap, rest, tail_nats(up2), best)

def osa_rows(s: String, ap: Maybe<&2, Char>, +i: Nat, +b: String,
    +prev: List<&2, Nat>, prev2: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case SNil{}: prev
    case SCon{+a, tail}:
      osa_rows(tail, Some{a}, (i + 1n : Nat), b,
        i <> osa_row(b, None{}, a, ap, prev, 0n <> prev2, i), prev)

def last_nat(xs: List<&2, Nat>, last: Nat) -> Nat:
  match xs:
    case Nil{}: last
    case head <> tail: last_nat(tail, head)

def osa(a: String, +b: String) -> Nat:
  +first = row_zero(b, 0n)
  last_nat(osa_rows(a, None{}, 1n, b, first, first), 0n)

def undashed(s: String) -> String:
  match s:
    case SCon{Chr{45}, tail}: undashed(tail)
    case _: s

def scored(names: List<&2, String>, +typed: String, +limit: Nat) ->
    List<&2, Scored>:
  match names:
    case Nil{}: Nil{}
    case +name <> tail:
      +dist = osa(typed, String.take(name, 64n))
      +rest = scored(tail, typed, limit)
      Bool.pick(List<&2, Scored>, Nat.is_le(dist, limit),
        Scored{dist, name} <> rest, rest)

def at_distance(found: List<&2, Scored>, +d: Nat) -> List<&2, String>:
  match found:
    case Nil{}: Nil{}
    case Scored{dist, name} <> tail:
      +rest = at_distance(tail, d)
      Bool.pick(List<&2, String>, Nat.is_eq(dist, d), name <> rest, rest)

def by_distance(levels: Nat, +d: Nat, +found: List<&2, Scored>) ->
    List<&2, String>:
  match levels:
    case 0n: Nil{}
    case 1n+more:
      List.append(&2, String, at_distance(found, d),
        by_distance(more, (d + 1n : Nat), found))

# At most 3 names within max(1, n / 3) edits, by distance, then order.
# key is bound because a temporary argument makes String.length take its
# string, adding a keep to each caller that reuses one (nat_fits, arg_display).
def suggest(+typed: String, names: List<&2, String>) -> List<&2, String>:
  key = undashed(typed)
  +limit = Nat.max(1n, Nat.div(String.length(key), 3n))
  List.take(&2, String, by_distance((limit + 1n : Nat), 0n,
    scored(names, String.take(typed, 64n), limit)), 3n)

# ---- Errors (§10.4) ----

def quoted(text: String, styles: List<&2, Style>) -> List<&2, Segment>:
  [plain("'"), Segment{text, styles}, plain("'")]

def missing_lines(missing: List<&2, String>) -> String:
  match missing:
    case Nil{}: ""
    case head <> tail: String.concat(["\n  ", head, missing_lines(tail)])

def visible_subs(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: ["help"]
    case Sub{name, about, children} <> tail:
      +rest = visible_subs(tail)
      Bool.pick(List<&2, String>, has_hidden(children), rest, name <> rest)
    case head <> tail: visible_subs(tail)

def fault_message(fault: ScanFault, path: String,
    items: List<&2, Item>) -> List<&2, Segment>:
  match fault:
    case E01{token}:
      List.concat(&2, Segment, [[plain("unexpected argument ")],
        quoted(token, [Yellow{}]), [plain(" found")]])
    case E02{name}:
      plain("unrecognized subcommand ") <> quoted(name, [Yellow{}])
    case E03{arg}:
      [plain(String.concat(["a value is required for '", arg,
        "' but none was supplied"]))]
    case E04{arg, value, reason}:
      List.concat(&2, Segment, [[plain("invalid value ")],
        quoted(value, [Yellow{}]),
        [plain(String.concat([" for '", arg, "': ", reason]))]])
    case E05{arg, value}:
      List.concat(&2, Segment, [[plain("unexpected value ")],
        quoted(value, [Yellow{}]),
        [plain(String.concat([" for '", arg,
          "' found; no more were expected"]))]])
    case E06{missing}:
      [plain(String.append(
        "the following required arguments were not provided:",
        missing_lines(missing)))]
    case E07{a, b}:
      [plain(String.concat(["the argument '", a, "' cannot be used with '", b,
        "'"]))]
    case E08{a, b}:
      [plain(String.concat(["the argument '", a, "' requires '", b, "'"]))]
    case E09{token}:
      List.concat(&2, Segment, [[plain("unexpected argument ")],
        quoted(token, [Yellow{}]), [plain(" found")]])
    case E10{}:
      [plain(String.concat(["'", path,
        "' requires a subcommand but none was provided\n  [subcommands: ",
        String.join(visible_subs(items), ", "), "]"]))]
    case E11{arg, value, name, reason}:
      List.concat(&2, Segment, [[plain("invalid value ")],
        quoted(value, [Yellow{}]),
        [plain(String.concat([" for '", arg, "' from environment variable ",
          name, ": ", reason]))]])

def green_names(names: List<&2, String>, first: Bool) -> List<&2, Segment>:
  match names:
    case Nil{}: Nil{}
    case name <> tail:
      List.concat(&2, Segment, [
        Bool.pick(List<&2, Segment>, first, [], [plain(", ")]),
        quoted(name, [Green{}]), green_names(tail, False{})])

def tip(text: String) -> List<&2, List<&2, Segment>>:
  [[plain(text)]]

# T4: one suggestion or several.
def similar(kind: String, found: List<&2, String>) ->
    List<&2, List<&2, Segment>>:
  match found:
    case Nil{}: Nil{}
    case name <> Nil{}:
      [plain(String.concat(["a similar ", kind, " exists: "])) <>
        quoted(name, [Green{}])]
    case name <> more:
      [plain(String.concat(["some similar ", kind, "s exist: "])) <>
        green_names(name <> more, True{})]

def long_name(s: String) -> Bool:
  String.starts_with(s, "--")

def option_names(parsed: Usage, attrs: List<&2, Item>) -> List<&2, String>:
  match parsed:
    case Parsed{id, short, +long, kind}:
      List.concat(&2, String, [
        Bool.pick(List<&2, String>, String.is_empty(long), [], [long]),
        Bool.pick(List<&2, String>,
          Bool.and(kind_negatable(kind), filled(long)),
          [negated_long(long)], []),
        List.filter(~String, ~long_name, find_aliases(attrs)),
      ])
    case Invalid{col}: []

def visible_names(hidden: Bool, usage: String, attrs: List<&2, Item>) ->
    List<&2, String>:
  match hidden:
    case True{}: []
    case False{}: option_names(parse_usage(usage), attrs)

# T4 for E01: visible longs, their no- forms and long aliases.
def long_candidates(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: Nil{}
    case Arg{usage, help, +attrs} <> tail:
      List.append(&2, String, visible_names(has_hidden(attrs), usage, attrs),
        long_candidates(tail))
    case head <> tail: long_candidates(tail)

# T4 for E02: visible subcommand names and aliases, then help.
def sub_candidates(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}: ["help"]
    case Sub{name, about, +children} <> tail:
      List.append(&2, String,
        Bool.pick(List<&2, String>, has_hidden(children), [],
          name <> find_aliases(children)),
        sub_candidates(tail))
    case head <> tail: sub_candidates(tail)

# T4 for E04: the one_of values of the arg E04 names.
def display_choices(items: List<&2, Item>, +arg: String,
    found: List<&2, String>) -> List<&2, String>:
  match items found:
    case _ head <> tail: head <> tail
    case Nil{} Nil{}: Nil{}
    case Arg{usage, help, +attrs} <> tail Nil{}:
      display_choices(tail, arg, Bool.pick(List<&2, String>,
        String.eq(arg_display(arg_info(usage, attrs)), arg),
        list_or_none(find_one_of(attrs)), []))
    case head <> tail Nil{}: display_choices(tail, arg, [])

def owned(found: Maybe<&2, OptFound>, text: String) -> Maybe<&2, String>:
  match found:
    case None{}: None{}
    case Some{option}: Some{text}

def owned_by(hit: Maybe<&2, OptFound>, token: String, prefix: String,
    step: String, found: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case None{}: found
    case Some{option}:
      Some{String.concat(["'", token, "' belongs to '", prefix,
        "'; place it before '", step, "'"])}

# T1: the deepest ancestor whose args take the long, and its child on path.
def owner(path: List<&2, String>, +items: List<&2, Item>, +prefix: String,
    +token: String, +long: String, found: Maybe<&2, String>) ->
    Maybe<&2, String>:
  match path:
    case Nil{}: found
    case +step <> tail:
      owner(tail, sub_items(find_sub(items, step)),
        String.concat([prefix, " ", step]), token, long,
        owned_by(find_option(items, long), token, prefix, step, found))

# T2: the first subcommand in pre-order whose args take the long.
def descendant(items: List<&2, Item>, +prefix: String, +long: String,
    found: Maybe<&2, String>) -> Maybe<&2, String>:
  match items found:
    case _ Some{path}: Some{path}
    case Nil{} None{}: None{}
    case Sub{name, about, +children} <> tail None{}:
      +path = String.concat([prefix, " ", name])
      descendant(tail, prefix, long, descendant(children, path, long,
        owned(find_option(children, long), path)))
    case head <> tail None{}: descendant(tail, prefix, long, None{})

def maybe_tip(found: Maybe<&2, String>) -> List<&2, List<&2, Segment>>:
  match found:
    case None{}: Nil{}
    case Some{text}: tip(text)

def belongs(found: Maybe<&2, String>, token: String) ->
    List<&2, List<&2, Segment>>:
  match found:
    case None{}: Nil{}
    case Some{path}:
      tip(String.concat(["'", token, "' belongs to subcommand '", path, "'"]))

def sub_exists(found: Maybe<&2, SubFound>, name: String) ->
    List<&2, List<&2, Segment>>:
  match found:
    case None{}: Nil{}
    case Some{sub}:
      tip(String.concat(["subcommand '", name,
        "' exists; to use it, remove the '--'"]))

def before_eq(s: String) -> String:
  match s:
    case SNil{}: SNil{}
    case SCon{Chr{61}, tail}: SNil{}
    case SCon{head, tail}: SCon{head, before_eq(tail)}

# T1, T2 and T3, for E01 on a long; --name=value looks up --name.
def long_tips(is_long: Bool, +token: String, root: String,
    path: List<&2, String>, +items: List<&2, Item>,
    root_items: List<&2, Item>, here: String) ->
    List<&2, List<&2, Segment>>:
  match is_long:
    case False{}: Nil{}
    case True{}:
      +long = before_eq(token)
      +name = String.drop(long, 2n)
      List.concat(&2, List<&2, Segment>, [
        maybe_tip(owner(path, root_items, root, token, long, None{})),
        belongs(descendant(items, here, long, None{}), token),
        sub_exists(find_sub(items, name), name),
      ])

def operand_count(events: List<&2, ScanEvent>, count: Nat) -> Nat:
  match events:
    case Nil{}: count
    case Enter{name} <> tail: operand_count(tail, 0n)
    case Operand{token} <> tail: operand_count(tail, (count + 1n : Nat))
    case event <> tail: operand_count(tail, count)

def trace_operands(trace: ScanTrace) -> Nat:
  match trace:
    case ScanTrace{path, events, ended, external, issue}:
      operand_count(events, 0n)

def dash_slot(open: Bool, +token: String) -> List<&2, List<&2, Segment>>:
  match open:
    case False{}: Nil{}
    case True{}:
      tip(String.concat(["to pass '", token, "' as a value, use '-- ", token,
        "'"]))

# T5: a hyphen token that the next positional slot could take after `--`;
# only then is argv scanned again to count the operands in scope.
def dash_tip(hyphen: Bool, token: String, items: List<&2, Item>, c: Cmd,
    argv: List<&2, String>) -> List<&2, List<&2, Segment>>:
  match hyphen:
    case False{}: Nil{}
    case True{}:
      dash_slot(positional_can_take(items, trace_operands(scan(c, argv))),
        token)

def cmd_items(c: Cmd) -> List<&2, Item>:
  match c:
    case Cmd{name, about, items}: items

# Every tip that applies, in table order.
def fault_tips(fault: ScanFault, +c: Cmd, +path: List<&2, String>,
    argv: List<&2, String>, here: String, +items: List<&2, Item>,
    globals: List<&2, Item>) -> List<&2, List<&2, Segment>>:
  match fault:
    case E01{+token}:
      List.concat(&2, List<&2, Segment>, [
        long_tips(long_name(token), token, cmd_name(c), path, items,
          cmd_items(c), here),
        similar("argument", suggest(token, List.concat(&2, String, [
          long_candidates(List.append(&2, Item, items, globals)),
          ["--help"],
          Bool.pick(List<&2, String>, Bool.and(List.is_empty(&2, String, path),
            has_version_item(items)), ["--version"], []),
        ]))),
        dash_tip(String.starts_with(token, "-"), token, items, c, argv),
      ])
    case E02{+name}: similar("subcommand", suggest(name, sub_candidates(items)))
    case E04{+arg, +value, reason}:
      similar("value", suggest(value,
        display_choices(List.append(&2, Item, items, globals), arg, [])))
    case E09{+token}:
      dash_tip(String.starts_with(token, "-"), token, items, c, argv)
    case _: Nil{}

def tip_spans(tips: List<&2, List<&2, Segment>>) -> List<&2, Segment>:
  match tips:
    case Nil{}: Nil{}
    case line <> tail:
      List.concat(&2, Segment, [
        [plain("  "), Segment{"tip:", [Bold{}, Green{}]}, plain(" ")],
        line, [plain("\n")], tip_spans(tail)])

def tip_block(tips: List<&2, List<&2, Segment>>) -> List<&2, Segment>:
  match tips:
    case Nil{}: Nil{}
    case head <> tail: plain("\n") <> tip_spans(head <> tail)

def error_page(message: List<&2, Segment>,
    tips: List<&2, List<&2, Segment>>, usage: List<&2, Segment>) ->
    List<&2, Segment>:
  List.concat(&2, Segment, [
    [Segment{"error:", [Bold{}, Red{}]}, plain(" ")], message, [plain("\n")],
    tip_block(tips), [plain("\n")], usage,
    [plain("\n\nFor more information, try '"), Segment{"--help", [Bold{}]},
      plain("'.\n")],
  ])

def fault_view(view: View, +fault: ScanFault, c: Cmd, path: List<&2, String>,
    argv: List<&2, String>, w: Nat) -> List<&2, Segment>:
  match view:
    case View{+here, about, +items, +globals, root, stuck}:
      error_page(fault_message(fault, here, items),
        fault_tips(fault, c, path, argv, here, items, globals),
        usage_block(usage_elems(here, items, globals), w))

# An error at the scope where scanning stopped, in stderr's colors.
def fault_err(t: Term, fault: ScanFault, +c: Cmd, +path: List<&2, String>,
    argv: List<&2, String>) -> String:
  match t:
    case Term{out_color, err_color, width}:
      emit(err_color, fault_view(view_of(c, path), fault, c, path, argv,
        page_width(width)))

def summary_err(t: Term, view: View) -> String:
  match t:
    case Term{out_color, err_color, width}:
      emit(err_color, help_page(view, False{}, page_width(width)))

# ---- Lint lines (§9) ----

def problem_line(p: Problem) -> String:
  match p:
    case BadUsage{at, usage, col}:
      String.concat(["  ", at, ": usage '", usage, "' is invalid at column ",
        Nat.show((col + 1n : Nat))])
    case BadName{at, name}:
      String.concat(["  ", at, ": '", name, "' is not a valid name"])
    case Dup{at, name}:
      String.concat(["  ", at, ": '", name, "' is declared more than once"])
    case Reserved{at, name}:
      String.concat(["  ", at, ": '", name, "' is reserved"])
    case Misplaced{at, attr}:
      String.concat(["  ", at, ": '", attr, "' is not allowed here"])
    case NoHelp{at, what}:
      String.concat(["  ", at, ": '", what, "' has no help text"])
    case BadDefault{at, id, value}:
      String.concat(["  ", at, ": '", id, "' cannot have the default '", value,
        "'"])
    case BadRef{at, id}:
      String.concat(["  ", at, ": '", id,
        "' is an unknown id or an unused or empty group"])
    case BadPositional{at, id, why}:
      String.concat(["  ", at, ": positional '", id, "': ", why])
    case Mixed{at}:
      String.concat(["  ", at, ": has both positionals and subcommands"])
    case BadChoices{at, id}:
      String.concat(["  ", at, ": one_of for '", id,
        "' is empty or repeats a value"])
    case NeedBare{at, id}:
      String.concat(["  ", at, ": '", id,
        "' needs [=<V>] and bare() together, with no short"])
    case DecodeBug{at, msg}:
      String.concat(["  ", at, ": decoder bug: ", msg])

def problem_lines(found: List<&2, Problem>) -> String:
  match found:
    case Nil{}: ""
    case p <> tail: String.concat([problem_line(p), "\n", problem_lines(tail)])

# ---- Outcome (§8.7, V1-V5) ----

type Outcome is Data:
  Shown{code: U32, out: String, err: String}
  Matched{m: Matches}

def find_version(items: List<&2, Item>) -> String:
  match items:
    case Nil{}: ""
    case Version{value} <> tail: value
    case head <> tail: find_version(tail)

def outcome_parse(result: ParseResult, +c: Cmd, h: Host,
    +argv: List<&2, String>) -> Outcome:
  match result:
    case Accepted{path, fields, external}:
      Matched{Matches{c, path, fields, external}}
    case HelpRequested{path, long}:
      Shown{0, help_out(term(c, h, argv), view_of(c, path), long), ""}
    case VersionRequested{}:
      Shown{0, String.concat([cmd_name(c), " ", find_version(cmd_items(c)),
        "\n"]), ""}
    case SummaryRequired{}:
      Shown{2, "", summary_err(term(c, h, argv), view_of(c, []))}
    case Rejected{path, fault}:
      Shown{2, "", fault_err(term(c, h, argv), fault, c, path, argv)}

def outcome_lint(found: List<&2, Problem>, +c: Cmd, +h: Host,
    +argv: List<&2, String>) -> Outcome:
  match found:
    case Nil{}: outcome_parse(parse(c, h, argv), c, h, argv)
    case p <> tail:
      Shown{70, "", String.append("bug: invalid command-line definition\n",
        problem_lines(p <> tail))}

# eval through V5: a lint failure, help, version, the V3 summary or an
# error is Shown; Matched is a parse left to decode.
def outcome(+c: Cmd, h: Host, argv: List<&2, String>) -> Outcome:
  outcome_lint(problems(c), c, h, argv)
