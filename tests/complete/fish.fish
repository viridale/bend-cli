# Purpose: ask fish what it completes at the end of each line of stdin,
# with SCRIPT loaded (§11); `complete -C` needs no terminal.
# Expected output: `<line> => <candidates>` per line, sorted, without their
# descriptions.
# Run: fish tests/complete/fish.fish SCRIPT < lines, in the directory the
#   lines' paths are relative to.
# Only SCRIPT completes: fish's own files for these names stay unloaded.
set -g fish_complete_path
source $argv[1]
while read -l line
    set -l words (complete -C "$line" | string replace -r '\t.*' '' | env LC_ALL=C sort)
    printf '%s => %s\n' $line (string join -- ' ' $words)
end
