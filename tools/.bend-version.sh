#!/usr/bin/env bash
# Shared advisory for tools pinned to a Bend release. Never blocks a tool.

bend_tools_latest_release() {
  local cache_dir=${XDG_CACHE_HOME:-${HOME:-/tmp}/.cache}/bend-tools
  local cache=$cache_dir/latest-release checked='' cached='' now body latest tmp
  now=$(date +%s)
  if [ -r "$cache" ]; then
    read -r checked cached <"$cache" || true
    if [[ $checked =~ ^[0-9]+$ && $cached =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] &&
      (( now >= checked && now - checked < 86400 )); then
      printf '%s\n' "$cached"
      return 0
    fi
  fi
  if command -v curl >/dev/null 2>&1 &&
    body=$(curl -fsSL --connect-timeout 1 --max-time 3 \
      -H 'Accept: application/vnd.github+json' \
      https://api.github.com/repos/bendlang/bend/releases/latest 2>/dev/null); then
    latest=$(printf '%s\n' "$body" |
      LC_ALL=C sed -nE 's/.*"tag_name"[[:space:]]*:[[:space:]]*"v([0-9]+\.[0-9]+\.[0-9]+)".*/\1/p' |
      head -n 1)
    if [ -n "$latest" ]; then
      if mkdir -p "$cache_dir" 2>/dev/null; then
        tmp=$(mktemp "$cache_dir/latest.XXXXXX" 2>/dev/null) || tmp=''
        if [ -n "$tmp" ]; then
          printf '%s %s\n' "$now" "$latest" >"$tmp"
          mv -f "$tmp" "$cache" 2>/dev/null || rm -f "$tmp"
        fi
      fi
      printf '%s\n' "$latest"
      return 0
    fi
  fi
  if [[ $cached =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then printf '%s\n' "$cached"; fi
  return 1
}

bend_tools_warn_version() {
  local pin=${1:-} tool=${2:-bend-tool} output installed='' latest=''
  if ! [[ $pin =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    printf '%s: invalid Bend version pin: %s\n' "$tool" "$pin" >&2
    return 0
  fi
  if output=$(bend version 2>/dev/null) &&
    [[ $output =~ ^bend[[:space:]]+([0-9]+\.[0-9]+\.[0-9]+)$ ]]; then
    installed=${BASH_REMATCH[1]}
    if [ "$installed" != "$pin" ]; then
      printf '%s: pinned to Bend %s; installed Bend is %s\n' "$tool" "$pin" "$installed" >&2
    fi
  else
    printf '%s: cannot read installed Bend version (pin %s)\n' "$tool" "$pin" >&2
  fi
  if latest=$(bend_tools_latest_release); then
    if [ "$latest" != "$pin" ]; then
      printf '%s: pinned to Bend %s; latest release is %s; review whether this tool is still needed\n' \
        "$tool" "$pin" "$latest" >&2
    fi
  else
    printf '%s: could not verify latest Bend release%s\n' "$tool" \
      "${latest:+ (cached $latest)}" >&2
    if [ -n "$latest" ] && [ "$latest" != "$pin" ]; then
      printf '%s: pinned to Bend %s; cached release is %s\n' "$tool" "$pin" "$latest" >&2
    fi
  fi
  return 0
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then
  bend_tools_warn_version "$@"
fi
