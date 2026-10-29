# Purpose: proofs of the grep example laws.
# Expected output: ALL PROOFS CHECK.
# Run: bend examples/grep/PROOF.bend --verdict

import Base
import ./app.bend as App
import ../../cli.bend as Cli
import ./LAWS.bend as Laws

# cli_ok in parts: --verdict's kernel gives each conversion its own fuel,
# and the lint and the decoder's 14 samples together take more than one
# has. check_nil takes the lint apart, and msgs_split the samples five at
# a time.
def check_nil(-c: Cli.Cmd,
    ep: {Cli.problems(c) == [] : List<&2, Cli.Problem>},
    eb: {Cli.sample_bugs(~App.Grep, ~App.decode, Cli.sample_paths(c), c)
      == [] : List<&2, Cli.Problem>}) ->
    {Cli.check(~App.Grep, ~App.decode, c) == [] : List<&2, Cli.Problem>}:
  %Equal.sym(List<&2, Cli.Problem>, Cli.problems(c), [], ep) :
    {List.append(&2, Cli.Problem, _, Cli.sample_bugs(~App.Grep,
      ~App.decode, Cli.sample_paths(c), c)) == [] : List<&2, Cli.Problem>}
  eb

# Empty at [], so a cons is not [].
def list_disc(xs: List<&2, String>) -> Data:
  match xs:
    case Nil{}: Empty
    case h <> t: Unit

def cons_nil_absurd(-h: String, -t: List<&2, String>,
    e: {h <> t == [] : List<&2, String>}) -> Empty:
  %e : list_disc(_)
  Unit{}

# xs ++ zs is empty when xs ++ ys is and zs is whenever ys is.
def append_nil_both(xs: List<&2, String>, -ys: List<&2, String>,
    -zs: List<&2, String>,
    e: {List.append(&2, String, xs, ys) == [] : List<&2, String>},
    f: {ys == [] : List<&2, String>} -> {zs == [] : List<&2, String>}) ->
    {List.append(&2, String, xs, zs) == [] : List<&2, String>}:
  match xs:
    case Nil{}: f(e)
    case h <> t:
      Empty.absurd({List.append(&2, String, h <> t, zs) == []
        : List<&2, String>},
        cons_nil_absurd(h, List.append(&2, String, t, ys), e))

# No sample's decode is a Bug if none of the first n's is and none of the
# rest's is.
def msgs_split(ms: List<&2, Cli.Matches>, n: Nat,
    ea: {Cli.sample_msgs(~App.Grep, ~App.decode,
      List.take(&2, Cli.Matches, ms, n)) == [] : List<&2, String>},
    eb: {Cli.sample_msgs(~App.Grep, ~App.decode,
      List.drop(&2, Cli.Matches, ms, n)) == [] : List<&2, String>}) ->
    {Cli.sample_msgs(~App.Grep, ~App.decode, ms) == [] : List<&2, String>}:
  match ms n:
    case Nil{} _: {==}
    case h <> t 0n: eb
    case h <> t 1n+p:
      append_nil_both(Cli.bug_msg(App.Grep, App.decode(h)),
        Cli.sample_msgs(~App.Grep, ~App.decode,
          List.take(&2, Cli.Matches, t, p)),
        Cli.sample_msgs(~App.Grep, ~App.decode, t), ea,
        e => msgs_split(t, p, e, eb))

# The root path's bugs, from its samples' messages.
def root_bugs(-c: Cli.Cmd,
    e: {Cli.sample_msgs(~App.Grep, ~App.decode, Cli.samples(c, []))
      == [] : List<&2, String>}) ->
    {Cli.sample_bugs(~App.Grep, ~App.decode, [[]], c)
      == [] : List<&2, Cli.Problem>}:
  %Equal.sym(List<&2, String>, Cli.sample_msgs(~App.Grep, ~App.decode,
    Cli.samples(c, [])), [], e) :
    {List.append(&2, Cli.Problem, Cli.decode_bugs(Cli.distinct(_, []),
      Cli.path_text(Cli.cmd_name(c), [])), Cli.sample_bugs(~App.Grep,
      ~App.decode, [], c)) == [] : List<&2, Cli.Problem>}
  {==}

def grep_problems() ->
    {Cli.problems(App.cli()) == [] : List<&2, Cli.Problem>}:
  {==}

def grep_msgs() -> {Cli.sample_msgs(~App.Grep, ~App.decode,
    Cli.samples(App.cli(), [])) == [] : List<&2, String>}:
  msgs_split(Cli.samples(App.cli(), []), 5n, {==},
    msgs_split(List.drop(&2, Cli.Matches, Cli.samples(App.cli(), []), 5n),
      5n, {==}, {==}))

def grep_bugs() -> {Cli.sample_bugs(~App.Grep, ~App.decode,
    Cli.sample_paths(App.cli()), App.cli()) == [] : List<&2, Cli.Problem>}:
  %Equal.sym(List<&2, List<&2, String>>, Cli.sample_paths(App.cli()), [[]],
    {==}) :
    {Cli.sample_bugs(~App.Grep, ~App.decode, _, App.cli())
      == [] : List<&2, Cli.Problem>}
  root_bugs(App.cli(), grep_msgs())

def Laws.cli_ok():
  check_nil(App.cli(), grep_problems(), grep_bugs())

def Laws.help_short():
  {==}

# eval of a spec that passes lint: the lint and the long help page take
# more than one conversion's fuel, so help_long checks the lint apart.
def linted_eval(-c: Cli.Cmd, -h: Cli.Host, -argv: List<&2, String>,
    -g: Cli.Step<App.Grep>,
    ep: {Cli.problems(c) == [] : List<&2, Cli.Problem>},
    e: {Cli.eval_step(App.Grep, App.decode, Cli.outcome_parse(
      Cli.parse(c, h, argv), c, h, argv), h, argv) == g
      : Cli.Step<App.Grep>}) ->
    {Cli.eval(~App.Grep, ~App.decode, c, h, argv) == g : Cli.Step<App.Grep>}:
  %Equal.sym(List<&2, Cli.Problem>, Cli.problems(c), [], ep) :
    {Cli.eval_step(App.Grep, App.decode, Cli.outcome_lint(_, c, h, argv), h,
      argv) == g : Cli.Step<App.Grep>}
  e

# The law's golden again: g is erased, but a call still names it.
def Laws.help_long():
  linted_eval(App.cli(), Cli.host(80n), ["--help"],
    Cli.Quit{0, String.concat([
      "Print lines that contain a pattern\n",
      "\n",
      "PATTERN is plain text, not a regular expression. Each FILE is read whole, so it\n",
      "must be a regular file under 2 GiB. With more than one FILE, each line starts\n",
      "with its file's name.\n",
      "\n",
      Laws.options(),
      "  -h, --help                Print help (see a summary with '-h')\n",
      Laws.sections(),
    ]), ""}, grep_problems(), {==})

def Laws.ignore_case():
  {==}

def Laws.env_max():
  {==}

def Laws.argv_max():
  {==}

def Laws.decode_flags():
  ({==}, ({==}, {==}))

def Laws.bad_max():
  {==}

def Laws.no_file():
  {==}

def Laws.one_mode():
  ({==}, {==})

def Laws.only_invert():
  {==}

def Laws.color_always():
  {==}

def Laws.found_exact():
  {==}

def Laws.found_fold_max():
  {==}

def Laws.found_none():
  {==}

def Laws.found_ascii_fold():
  {==}

def Laws.found_every_line():
  {==}

def Laws.found_paint():
  {==}

def Laws.found_filename():
  ({==}, ({==}, {==}))

def Laws.found_invert():
  ({==}, ({==}, ({==}, {==})))

def Laws.found_numbers():
  ({==}, ({==}, {==}))

def Laws.found_only():
  ({==}, ({==}, ({==}, {==})))

def Laws.found_count():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.found_names():
  ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.found_quiet():
  ({==}, {==})

def Laws.status(selected, quiet):
  match selected quiet:
    case True{} True{}: ({==}, ({==}, ({==}, ({==}, {==}))))
    case True{} False{}: ({==}, ({==}, ({==}, ({==}, {==}))))
    case False{} True{}: ({==}, ({==}, ({==}, ({==}, {==}))))
    case False{} False{}: ({==}, ({==}, ({==}, ({==}, {==}))))

def Laws.stops(failed, selected):
  match failed selected:
    case True{} True{}: ({==}, ({==}, {==}))
    case True{} False{}: ({==}, ({==}, {==}))
    case False{} True{}: ({==}, ({==}, {==}))
    case False{} False{}: ({==}, ({==}, {==}))
