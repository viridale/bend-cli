# Sourced by bash.zsh in the interactive bash: loads $BT_SCRIPT and wraps the
# completion function of $BT_CMD to append the words it offers, sorted, as
# one line of $BT_OUT.
PS1='$ '
bind 'set bell-style none'
source "$BT_SCRIPT"
bt_f=$(complete -p "$BT_CMD")
bt_f=${bt_f#*-F }
bt_f=${bt_f%% *}
_bt() {
  "$bt_f" "$@"
  local words
  mapfile -t words < <(printf '%s\n' "${COMPREPLY[@]}" | LC_ALL=C sort)
  printf '%s\n' "${words[*]}" >> "$BT_OUT"
}
complete -F _bt "$BT_CMD"
: > "$BT_OUT.ready"
