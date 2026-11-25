#!/usr/bin/env bash
# Regenerate every committed certificate into a temporary directory with the generator in
# `certgen/` (default settings) and check that the result is identical to the committed files.
#   usage: scripts/check-regen.sh [types...]      e.g. scripts/check-regen.sh "5 0" "0 3"
set -euo pipefail
cd "$(dirname "$0")/.."
types=("$@")
if [ ${#types[@]} -eq 0 ]; then
  types=("0 0" "1 0" "0 1" "2 0" "1 1" "3 0" "0 2" "2 1" "4 0" "1 2" "3 1" "5 0" "0 3" "2 2" "4 1")
fi
(cd certgen && cargo build --release --quiet)
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
status=0
for ty in "${types[@]}"; do
  set -- $ty
  k=$((1 + $1 + 2 * $2))
  dir="Solution/Atoms$k/S$1N$2"
  scripts/safe-run.sh 30G 7200 certgen/target/release/certgen gen "$1" "$2" "$tmp" > /dev/null
  if diff -r "$tmp/$dir" "$dir" > /dev/null; then
    echo "($1,$2): identical to $dir"
  else
    echo "($1,$2): DIFFERS from $dir"
    status=1
  fi
done
exit $status
