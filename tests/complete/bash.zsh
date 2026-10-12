#!/bin/zsh -f
# Purpose: drive a real interactive bash through a pty: source SCRIPT, type
# each line of stdin, press TAB once, and record what CMD's completion
# function left in COMPREPLY (§11). Readline splits the line, so this sees
# COMP_WORDBREAKS as users do.
# Expected output: `<line> => <words>` per line, the words sorted.
# Run: tests/complete/bash.zsh SCRIPT CMD < lines, in the directory the
#   lines' paths are relative to. BASH_CMD (default bash) is the command
#   that starts bash; this directory, SCRIPT's and this file's must be
#   visible to it at the same paths. bash.out next to SCRIPT holds the words.
zmodload zsh/zpty zsh/zselect
BT_OUT=${1:A:h}/bash.out
: > $BT_OUT
rm -f $BT_OUT.ready
zpty B ${=BASH_CMD:-bash} --norc --noprofile -i
zpty -w B "cd ${(qq)PWD} && BT_SCRIPT=${(qq)1:A} BT_CMD=${(qq)2} BT_OUT=${(qq)BT_OUT} && source ${(qq)${0:A:h}}/bash_init.bash"
# Reads bash's echo as it comes, or bash blocks on a full pty.
await() {
  local t
  for t in {1..600}; do
    while zpty -rt B junk; do :; done
    eval "$1" && return 0
    zselect -t 5
  done
  print -u2 "bash.zsh: timed out on: $line"
  exit 1
}
line=init
await '[[ -e $BT_OUT.ready ]]'
n=0
while IFS= read -r line; do
  (( n++ ))
  zpty -w -n B "$line"$'\t'
  await '(( $(wc -l < $BT_OUT) >= n ))'
  print -r -- "$line => $(sed -n ${n}p $BT_OUT)"
  zpty -w -n B $'\C-a\C-k'
done
zpty -d B
rm -f $BT_OUT $BT_OUT.ready
