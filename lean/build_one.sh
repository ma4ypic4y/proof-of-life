#!/bin/sh
# build_one.sh <module>: lake build one module, append "<module> <rc> <seconds>" to logs/times.txt
cd "$(dirname "$0")"
m="$1"
if [ -f "skip/$m" ]; then echo "$m skipped (marker)"; exit 0; fi
s=$(python3 -c "import time; print(time.time())")
"$HOME/.elan/bin/lake" build "$m" > "logs/$m.log" 2>&1; rc=$?
e=$(python3 -c "import time; print(time.time())")
echo "$m $rc $(python3 -c "print(round($e-$s,1))")" >> logs/times.txt
echo "$m rc=$rc"
