// The argbench command (examples/argbench/app.bend) in commander, run with
// Bun: it prints the line the Bend app prints for each argv
// tools/peerbench.sh checks.
import { Command, InvalidArgumentError, Option } from "commander";

function u32(value) {
  if (!/^[0-9]+$/.test(value) || Number(value) > 4294967295) {
    throw new InvalidArgumentError("expected a whole number from 0 to 4294967295");
  }
  return Number(value);
}

// commander documents prev.concat([value]), which copies the list for
// every value; a push keeps a long argv linear.
function collect(value, prev) {
  prev.push(value);
  return prev;
}

const program = new Command("argbench")
  .description("Print the line an argv decodes to")
  // Usage errors exit 2, as in bend-cli; commander exits 1.
  .exitOverride();

program
  .command("build")
  .description("Build inputs")
  .option("-v, --verbose", "More output; repeat for more", (_, prev) => prev + 1, 0)
  .option("-q, --quiet", "Less output", false)
  .option("-o, --output <FILE>", "Write the result to FILE", "out")
  .option("-I, --include <DIR>", "Search DIR for inputs", collect, [])
  .option("-j, --jobs <N>", "Run N jobs at once", u32, 1)
  .addOption(new Option("-f, --format <FMT>", "Output format")
    .choices(["text", "json", "csv"]).default("text"))
  .argument("<INPUT...>", "Files to build")
  .action((inputs, o) => {
    console.log(`build verbose=${o.verbose} quiet=${o.quiet} output=${o.output} ` +
      `include=${o.include.join(",")} jobs=${o.jobs} format=${o.format} ` +
      `inputs=${inputs.join(",")}`);
  });

program
  .command("check")
  .description("Check inputs")
  .option("-s, --strict", "Treat warnings as errors", false)
  .argument("<INPUT...>", "Files to check")
  .action((inputs, o) => {
    console.log(`check strict=${o.strict} inputs=${inputs.join(",")}`);
  });

try {
  program.parse();
} catch (e) {
  process.exit(e.exitCode === 0 ? 0 : 2);
}
