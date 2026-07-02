#!/usr/bin/env bash
#
# keynote-demo.sh — the stage demo for reasonable reflection, one entry
# point, presenter-paced, with a recorded fallback for the live LLM beat.
#
#   ./demo/keynote-demo.sh              # live LLM in beat 3 (needs Bedrock)
#   ./demo/keynote-demo.sh --offline    # replay the recorded run (no network)
#   ./demo/keynote-demo.sh --no-pause    # run straight through (rehearsal)
#
# Beats:
#   1  the gate: admit with evidence, refuse without (demoGuarded)
#   2  stacking: two admitted modifications live at once (demoStack)
#   3  the proposer: an LLM proposes, the kernel decides (booth llm)
#
# Assumes the binaries are built: `lake build demoGuarded demoStack booth`.
# Beats 1 and 2 are deterministic and need no network. Beat 3 is live and
# non-deterministic; on any failure (or with --offline) it replays
# demo/recorded-llm-run.txt.

set -uo pipefail
cd "$(dirname "$0")/.."

BIN=".lake/build/bin"
RECORDED="demo/recorded-llm-run.txt"
OFFLINE=0
PAUSE=1
BRIEF="Make pairs (cons cells) applicable: applying a pair to arguments returns the pair's car. The pair? guard is not pre-proved, so prove its GuardSpec yourself. Include two tests."

for arg in "$@"; do
  case "$arg" in
    --offline)  OFFLINE=1 ;;
    --no-pause) PAUSE=0 ;;
    *) echo "unknown flag: $arg"; exit 2 ;;
  esac
done

# Colors (fall back to plain if not a terminal).
if [ -t 1 ]; then
  C=$'\033[1;36m'; D=$'\033[2m'; Z=$'\033[0m'
else
  C=""; D=""; Z=""
fi

need() {
  if [ ! -x "$BIN/$1" ]; then
    echo "missing $BIN/$1 — run:  lake build $1" >&2
    exit 1
  fi
}
need demoGuarded; need demoStack; need booth

banner() { printf '\n%s========================================================%s\n' "$C" "$Z"
           printf '%s  %s%s\n' "$C" "$1" "$Z"
           printf '%s========================================================%s\n\n' "$C" "$Z"; }

pause() {
  [ "$PAUSE" = 1 ] || return 0
  printf '\n%s— enter to continue —%s' "$D" "$Z"
  read -r _ || true
  printf '\n'
}

banner "1.  The gate: admit with evidence, refuse without"
"$BIN/demoGuarded"
pause

banner "2.  Stacking: two admitted modifications live at once"
"$BIN/demoStack"
pause

banner "3.  The proposer: an LLM proposes, the kernel decides"
if [ "$OFFLINE" = 1 ]; then
  printf '%s[offline — replaying a recorded live run]%s\n\n' "$D" "$Z"
  cat "$RECORDED"
else
  if ! "$BIN/booth" llm "$BRIEF"; then
    printf '\n%s[live call did not land — replaying a recorded run]%s\n\n' "$D" "$Z"
    [ -f "$RECORDED" ] && cat "$RECORDED"
  fi
fi

banner "The proposer may be wild. The gate is narrow. The change is kernel-checked."
