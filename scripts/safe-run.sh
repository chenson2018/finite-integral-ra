#!/usr/bin/env bash
# Run a command under a hard memory cap and a wall-clock timeout, so that a runaway
# kernel reduction or search cannot take the machine down.
#   usage: scripts/safe-run.sh <mem, e.g. 12G> <timeout seconds> <command...>
set -euo pipefail
mem="$1"; shift
secs="$1"; shift
exec systemd-run --user --scope -q -p MemoryMax="$mem" -p MemorySwapMax=0 \
  timeout --kill-after=10 "$secs" "$@"
