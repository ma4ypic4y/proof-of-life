#!/bin/sh
# Timed parallel build: build_timed.sh <parallelism> <deps...> -- <modules...>
# Builds <deps> first (one lake invocation), then each module in its own
# `lake build <module>` (in parallel), recording wall-clock seconds per module
# in logs/times.txt as "<module> <exit code> <seconds>".
set -u
cd "$(dirname "$0")"
LAKE="$HOME/.elan/bin/lake"
P="$1"; shift
DEPS=""
while [ "$#" -gt 0 ] && [ "$1" != "--" ]; do DEPS="$DEPS $1"; shift; done
[ "$#" -gt 0 ] && shift
mkdir -p logs
if [ -n "$DEPS" ]; then
  $LAKE build $DEPS > logs/deps.log 2>&1 || { echo "deps failed"; tail -30 logs/deps.log; exit 1; }
fi
: > logs/times.txt
for m in "$@"; do echo "$m"; done | xargs -P "$P" -n 1 ./build_one.sh
cat logs/times.txt
