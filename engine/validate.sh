#!/bin/zsh
# Byte-exact validation of tol (fast), tol_naive and Google's cubff reference.
# Every checkpoint of every run must be identical across all three.
set -e
cd "${0:A:h}"
B=${BROTLI:-$(brew --prefix brotli)}
cc -O3 -mcpu=native -Wall -I$B/include tol.c -L$B/lib -lbrotlienc -lm -o tol
cc -O3 -mcpu=native -Wall -DNAIVE -I$B/include tol.c -L$B/lib -lbrotlienc -lm -o tol_naive
CUBFF=${CUBFF:?set CUBFF to a cubff binary built with CUDA=0 (see README)}
W=/tmp/tol_validate; rm -rf $W; mkdir -p $W
python3 - <<PY
# A soup seeded with the paper's hand-written replicator (Fig. 4, zero-byte filler)
# in 1 of every 16 slots, so the post-transition regime is exercised too.
import struct, random
random.seed(5)
rep = b"[[{.>]-]" + b"\x00"*48 + b"]-]>.{[["
assert len(rep) == 64
n = 8192
soup = bytearray()
for i in range(n):
    soup += rep if i % 16 == 0 else bytes(random.randrange(256) for _ in range(64))
open("$W/seeded.dat","wb").write(struct.pack("=QQQ", 0, n, 0) + soup)
PY
run() {  # name, cubff-args, tol-args
  local name=$1 cargs=$2 targs=$3
  mkdir -p $W/$name/{c,f,n}
  ( time $CUBFF ${=cargs} --checkpoint_dir $W/$name/c --save_interval 64 --print_interval 64 --disable_output ) 2>&1 | grep total | sed "s/^/  cubff  /"
  ( time ./tol ${=targs} --checkpoint-dir $W/$name/f --checkpoint-every 64 --threshold 99 ) 2>&1 | grep total | sed "s/^/  fast   /"
  ( time ./tol_naive ${=targs} --checkpoint-dir $W/$name/n --checkpoint-every 64 --threshold 99 ) 2>&1 | grep total | sed "s/^/  naive  /"
  local ok=0 bad=0
  for f in $(ls $W/$name/f); do
    # Compare soup bytes only: cubff copies the header's reset_index from a loaded file.
    if cmp -s -i 24 $W/$name/f/$f $W/$name/n/$f && cmp -s -i 24 $W/$name/f/$f $W/$name/c/$f; then ok=$((ok+1)); else bad=$((bad+1)); echo "  MISMATCH $f"; fi
  done
  echo "$name: $ok checkpoints identical, $bad mismatches"
}
run noheads   "--lang bff_noheads --num 8192 --seed 3 --max_epochs 3000" "--num 8192 --seed 3 --max-epochs 3001"
run heads     "--lang bff --num 8192 --seed 4 --max_epochs 3000"         "--heads --num 8192 --seed 4 --max-epochs 3001"
run nomut     "--lang bff_noheads --num 8192 --seed 5 --max_epochs 2000 --mutation_prob 0" "--num 8192 --seed 5 --max-epochs 2001 --mut 0"
run seeded    "--lang bff_noheads --seed 6 --max_epochs 1500 --load $W/seeded.dat" "--seed 6 --max-epochs 1501 --load $W/seeded.dat"
