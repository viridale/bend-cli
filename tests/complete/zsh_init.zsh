# Sourced by zsh.zsh in the interactive zsh: autoloads the completion
# functions in $ZT_FPATH and wraps compadd to record in $ZT_OUT each word it
# adds, as zsh would insert it.
PS1=''
PROMPT=''
fpath=($ZT_FPATH $fpath)
autoload -Uz compinit
compinit -u -D
zstyle ':completion:*' completer _complete
bindkey '^I' complete-word
compadd() {
  # -O, -A and -D only fill arrays; let them through.
  if [[ ${@[1,(i)(-|--)]} == *-(O|A|D)\ * ]]; then
    builtin compadd "$@"
    return
  fi
  local -a hits
  local p
  (( $@[(I)-p] )) && p=${@[$(( ${@[(i)-p]} + 1 ))]}
  builtin compadd -A hits "$@"
  # _describe adds empty matches to lay out its list; they insert nothing.
  hits=(${hits:#})
  (( $#hits )) && print -rl -- $IPREFIX$p${^hits} >> $ZT_OUT
  # Add them too, or _files falls back to its next tag as if none matched.
  builtin compadd "$@"
}
: > $ZT_OUT.ready
