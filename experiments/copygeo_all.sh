#!/bin/zsh
# Soup-wide copy geometry for every living world, plus pre-life controls.
# usage: experiments/copygeo_all.sh [dir]   (default: data/, where experiments/atlas.py writes atlas/ and atlas_heads/)
# Needs engine/tol and engine/copygeo (see README) and the atlas runs' final soups (<dir>/atlas*/final/*.dat).
setopt nullglob
ROOT=${0:A:h}/..
RUNS=${1:-$ROOT/data}
E=$ROOT/engine
OUT=$ROOT/data/copygeo.jsonl; : > $OUT
C=$RUNS/controls; mkdir -p $C
# controls: soups after 1 epoch and after 2,048 epochs of worlds that never came alive
for s in 1 3; do [ -f $C/noheads_${s}_2048.dat ] || $E/tol --seed $s --max-epochs 2049 --threshold 99 --save-at 1,2048 --save-prefix $C/noheads_${s}_ > /dev/null; done
for s in 1001 1006; do [ -f $C/heads_${s}_2048.dat ] || $E/tol --heads --seed $s --max-epochs 2049 --threshold 99 --save-at 1,2048 --save-prefix $C/heads_${s}_ > /dev/null; done
# accidental copy loops are rare before life, so the controls sample many more pairs
for f in $C/noheads_*.dat; do $E/copygeo $f --pairs 65536 | sed 's/^{/{"set":"control-noheads",/' >> $OUT; done
for f in $C/heads_*.dat; do $E/copygeo $f --pairs 65536 --heads | sed 's/^{/{"set":"control-heads",/' >> $OUT; done
for f in $RUNS/atlas/final/*.dat; do $E/copygeo $f --pairs 4096 | sed 's/^{/{"set":"alive-noheads",/' >> $OUT; done
for f in $RUNS/atlas_heads/final/*.dat; do $E/copygeo $f --pairs 4096 --heads | sed 's/^{/{"set":"alive-heads",/' >> $OUT; done
python3 $ROOT/analysis/copygeo_agg.py
