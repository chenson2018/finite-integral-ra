#!/usr/bin/env bash
# Run a command under a hard memory cap and a wall-clock timeout, so that a runaway
# kernel reduction or search cannot take the machine down.
#   usage: scripts/safe-run.sh <mem, e.g. 12G> <timeout seconds> <command...>
#
# The glibc malloc settings below make the Lean kernel's big-number arithmetic (GMP) reuse heap
# memory instead of mapping and unmapping every large block, which saves a good part of the
# system time spent in page faults when checking the truth-table certificates.
set -euo pipefail
mem="$1"; shift
secs="$1"; shift
export MALLOC_MMAP_THRESHOLD_="${MALLOC_MMAP_THRESHOLD_:-4294967296}"
export MALLOC_TRIM_THRESHOLD_="${MALLOC_TRIM_THRESHOLD_:-4294967296}"
export MALLOC_TOP_PAD_="${MALLOC_TOP_PAD_:-1073741824}"
exec systemd-run --user --scope -q -p MemoryMax="$mem" -p MemorySwapMax=0 \
  timeout --kill-after=10 "$secs" "$@"
