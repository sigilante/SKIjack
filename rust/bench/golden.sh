#!/usr/bin/env bash
# Run one CLI over the whole corpus with every flag; write one file per
# invocation (stdout, then "--- exit N", then stderr) under OUTDIR.
#   bench/golden.sh "<runner command>" OUTDIR [JOBS]
# With NAMES_FROM=<a previous OUTDIR>, also lifts every compiled name and
# runs every level-1 declaration that the reference run listed.
# Runs from python/ so the file paths printed in messages agree.
set -u
RUNNER="$1"; OUT="$2"; JOBS="${3:-16}"
cd "$(dirname "$0")/../../python" || exit 1
mkdir -p "$OUT"
LIST="$OUT/.invocations"
: > "$LIST"
for f in skijack/corpus/*.ski; do
  b=$(basename "$f" .ski)
  echo "$b|summary|$f" >> "$LIST"
  for flag in --check --expand --dictionary "--render ascii" "--render unicode"; do
    echo "$b|${flag// /_}|$f $flag" >> "$LIST"
  done
  if [ -n "${NAMES_FROM:-}" ] && [ -f "$NAMES_FROM/$b/--expand.out" ]; then
    awk '/^--- exit/{exit} {print $2}' "$NAMES_FROM/$b/--expand.out" | while read -r nm; do
      [ -n "$nm" ] && echo "$b|--lift_$nm|$f --lift $nm" >> "$LIST"
    done
    awk '/^--- exit/{exit} /^    [^ ]+ = /{print $1}' "$NAMES_FROM/$b/summary.out" | while read -r nm; do
      echo "$b|--run_$nm|$f --run $nm" >> "$LIST"
      echo "$b|--run_${nm}_fuel1|$f --run $nm --fuel 1" >> "$LIST"
    done
    echo "$b|--run_sp|$f --run sp" >> "$LIST"
    echo "$b|--run_nope|$f --run nope" >> "$LIST"
    echo "$b|--lift_nope|$f --lift nope" >> "$LIST"
  fi
done
run_one() {
  local line="$1"; local b="${line%%|*}"; local rest="${line#*|}"; local slug="${rest%%|*}"; local cmd="${rest#*|}"
  mkdir -p "$OUT/$b"
  local o="$OUT/$b/$slug.out"
  # shellcheck disable=SC2086
  $RUNNER $cmd > "$o.stdout" 2> "$o.stderr"; local code=$?
  { cat "$o.stdout"; echo "--- exit $code"; cat "$o.stderr"; } > "$o"
  rm -f "$o.stdout" "$o.stderr"
}
export -f run_one; export RUNNER OUT
[ -n "${LIST_ONLY:-}" ] && { echo "$(wc -l < "$LIST") invocations listed -> $LIST"; exit 0; }
xargs -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {} < "$LIST"
echo "$(wc -l < "$LIST") invocations -> $OUT"
