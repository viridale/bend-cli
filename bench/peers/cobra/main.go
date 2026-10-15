// The argbench command (examples/argbench/app.bend) in cobra: it prints the
// line the Bend app prints for each argv tools/peerbench.sh checks.
package main

import (
	"fmt"
	"os"
	"strings"

	"github.com/spf13/cobra"
)

// format is a pflag value that accepts only the three formats, so a bad
// one fails while parsing, as one_of does in bend-cli.
type format string

func (f *format) String() string { return string(*f) }
func (f *format) Type() string   { return "FMT" }
func (f *format) Set(s string) error {
	switch s {
	case "text", "json", "csv":
		*f = format(s)
		return nil
	}
	return fmt.Errorf("expected one of 'text', 'json', 'csv'")
}

func build() *cobra.Command {
	var (
		verbose int
		quiet   bool
		output  string
		include []string
		jobs    uint32
		fmtName = format("text")
	)
	cmd := &cobra.Command{
		Use:   "build <INPUT>...",
		Short: "Build inputs",
		Args:  cobra.MinimumNArgs(1),
		Run: func(cmd *cobra.Command, inputs []string) {
			fmt.Printf("build verbose=%d quiet=%t output=%s include=%s jobs=%d format=%s inputs=%s\n",
				verbose, quiet, output, strings.Join(include, ","), jobs, fmtName,
				strings.Join(inputs, ","))
		},
	}
	f := cmd.Flags()
	f.CountVarP(&verbose, "verbose", "v", "More output; repeat for more")
	f.BoolVarP(&quiet, "quiet", "q", false, "Less output")
	f.StringVarP(&output, "output", "o", "out", "Write the result to FILE")
	f.StringArrayVarP(&include, "include", "I", nil, "Search DIR for inputs")
	f.Uint32VarP(&jobs, "jobs", "j", 1, "Run N jobs at once")
	f.VarP(&fmtName, "format", "f", "Output format (text, json, csv)")
	return cmd
}

func check() *cobra.Command {
	var strict bool
	cmd := &cobra.Command{
		Use:   "check <INPUT>...",
		Short: "Check inputs",
		Args:  cobra.MinimumNArgs(1),
		Run: func(cmd *cobra.Command, inputs []string) {
			fmt.Printf("check strict=%t inputs=%s\n", strict, strings.Join(inputs, ","))
		},
	}
	cmd.Flags().BoolVarP(&strict, "strict", "s", false, "Treat warnings as errors")
	return cmd
}

func main() {
	root := &cobra.Command{
		Use:   "argbench",
		Short: "Print the line an argv decodes to",
		// With no command, the help goes to stderr as an error, as in
		// bend-cli; cobra would print it to stdout and exit 0.
		RunE: func(cmd *cobra.Command, args []string) error {
			cmd.SetOut(os.Stderr)
			cmd.Help()
			os.Exit(2)
			return nil
		},
	}
	root.CompletionOptions.DisableDefaultCmd = true
	root.AddCommand(build(), check())
	// Usage errors exit 2, as in bend-cli; cobra leaves the code to main.
	if root.Execute() != nil {
		os.Exit(2)
	}
}
