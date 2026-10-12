#!/bin/zsh -f
# Purpose: drive a real interactive zsh through a pty with the completion
# function in FPDIR autoloaded: type each line of stdin, press TAB once, and
# record each word the function offers, as zsh would insert it (§11).
# Expected output: `<line> => <words>` per line, the words sorted.
# Run: tests/complete/zsh.zsh FPDIR < lines, in the directory the lines'
#   paths are relative to; zsh.out next to FPDIR holds the words.
zmodload zsh/zpty zsh/zselect
ZT_OUT=${1:A:h}/zsh.out
: > $ZT_OUT
rm -f $ZT_OUT.ready
zpty Z zsh -f -i
zpty -w Z "ZT_FPATH=${(qq)1:A} ZT_OUT=${(qq)ZT_OUT} && source ${(qq)${0:A:h}}/zsh_init.zsh"
await() {
  local t
  for t in {1..600}; do
    while zpty -rt Z junk; do :; done
    eval "$1" && return 0
    zselect -t 5
  done
  print -u2 "zsh.zsh: timed out on: $line"
  exit 1
}
line=init
await '[[ -e $ZT_OUT.ready ]]'
n=0
while IFS= read -r line; do
  (( n++ ))
  zpty -w -n Z "$line"$'\t'
  zpty -w -n Z $'\C-a\C-k'
  # The shell runs this only after the completion, so __DONE__ ends its
  # matches; the typed text is not the marker, since ${:-} expands.
  zpty -w Z 'print -r -- __D${:-ONE}__ >> $ZT_OUT'
  await '(( $(grep -c "^__DONE__$" $ZT_OUT) >= n ))'
  words=(${(f)"$(awk -v n=$n '/^__DONE__$/ { k++; next } k == n - 1' $ZT_OUT |
    LC_ALL=C sort -u)"})
  print -r -- "$line => ${(j: :)words}"
done
zpty -d Z
rm -f $ZT_OUT $ZT_OUT.ready
