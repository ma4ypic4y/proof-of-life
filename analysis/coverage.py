#!/usr/bin/env python3
"""Share of a living world's final soup that belongs to its top genome's lineage,
per orientation (+ = genome, - = reversed genome), by identity at the genome's
instruction positions (>= 80%). usage: coverage.py <atlas_dir> > coverage.jsonl"""
import glob, json, os, sys
OPS = set(b"<>{}+-.,[]")
atlas = sys.argv[1]
for f in sorted(glob.glob(os.path.join(atlas, "final", "*.dat"))):
    seed = os.path.basename(f)[:-4]
    top = [json.loads(l) for l in open(os.path.join(atlas, "census", f"{seed}.jsonl"))][-1]["top"]
    reps = [t for t in top if t["selfrep"] >= 5]
    if not reps:
        continue
    p = bytes.fromhex(reps[0]["hex"]); r = p[::-1]
    ip = [i for i in range(64) if p[i] in OPS]; ir = [i for i in range(64) if r[i] in OPS]
    raw = open(f, "rb").read()[24:]
    n = len(raw) // 64; plus = minus = 0
    for t in range(n):
        q = raw[t * 64:(t + 1) * 64]
        a = sum(q[i] == p[i] for i in ip) / len(ip); b = sum(q[i] == r[i] for i in ir) / len(ir)
        if a >= 0.8 and a >= b: plus += 1
        elif b >= 0.8: minus += 1
    print(json.dumps({"seed": int(seed), "n": n, "plus": plus, "minus": minus, "palindrome_like": p == r}), flush=True)
