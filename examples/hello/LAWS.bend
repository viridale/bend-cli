# Purpose: laws for the hello example, the README quickstart: the definition
# check, the help page and how argv decodes or fails.
# Expected output: ALL PROOFS CHECK.
# Run: bend examples/hello/PROOF.bend --verdict

import Base
import ./app.bend as App
import ../../cli.bend as Cli

law cli_ok:
  {Cli.check(~App.Greeting, ~App.decode, App.cli()) == []
    : List<&2, Cli.Problem>}

law default_name:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), [])
    == Cli.Go{App.Greeting{"world"}, Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Greeting>}

law given_name:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), ["Ada"])
    == Cli.Go{App.Greeting{"Ada"}, Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Greeting>}

def page() -> String:
  String.concat([
    "Print a greeting\n",
    "\n",
    "Usage: hello [NAME]\n",
    "\n",
    "Arguments:\n",
    "  [NAME]      Who to greet [default: world]\n",
    "\n",
    "Options:\n",
    "  -h, --help  Print help\n",
  ])

# Each text has one paragraph, so -h and --help print the same page.
law help:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), ["-h"])
    == Cli.Exit{0, page(), ""} : Cli.Step<App.Greeting>} &
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), ["--help"])
    == Cli.Exit{0, page(), ""} : Cli.Step<App.Greeting>}

law second_name:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n),
    ["Ada", "Bo"])
    == Cli.Exit{2, "", String.concat([
      "error: unexpected argument 'Bo' found\n",
      "\n",
      "Usage: hello [NAME]\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Greeting>}

# hello has no options, so an option is an error whose tip shows how to
# pass it as the name.
law option:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n),
    ["--name", "Ada"])
    == Cli.Exit{2, "", String.concat([
      "error: unexpected argument '--name' found\n",
      "\n",
      "  tip: to pass '--name' as a value, use '-- --name'\n",
      "\n",
      "Usage: hello [NAME]\n",
      "\n",
      "For more information, try '--help'.\n",
    ])} : Cli.Step<App.Greeting>}
