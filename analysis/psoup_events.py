#!/usr/bin/env python3
"""Classify every interaction of a prompt-soup run.

For a pair (A = system prompt, B = user message) -> B', compare B' to A and
to the old B with character 5-gram Jaccard similarity:
  copy     : B' resembles A more than B, and sim(B', A) >= 0.3  (A wrote itself into B's slot)
  persist  : B' resembles B more than A, and sim(B', B) >= 0.3  (B's lineage survives)
  novel    : neither
Copy events are what increases a text's copy number — replication.
"""
import json, sys

def grams(s, k=5):
    s = s.lower()
    return {s[i:i + k] for i in range(max(1, len(s) - k + 1))}

def jac(a, b):
    return len(a & b) / max(1, len(a | b))

rows = [json.loads(l) for l in open(sys.argv[1])]
prev = rows[0]["texts"]
print("epoch  copy  persist  novel   mean_sim(B',A)  mean_sim(B',B)")
for r in rows[1:]:
    cur = r["texts"]
    c = p = n = 0; sa = sb = 0.0
    for a, b in r["pairs"]:
        ga, gb, gn = grams(prev[a]), grams(prev[b]), grams(cur[b])
        s_a, s_b = jac(gn, ga), jac(gn, gb)
        sa += s_a; sb += s_b
        if s_a > s_b and s_a >= 0.3: c += 1
        elif s_b >= s_a and s_b >= 0.3: p += 1
        else: n += 1
    k = len(r["pairs"])
    print(f"{r['epoch']:5d} {c:5d} {p:8d} {n:6d}   {sa / k:14.3f} {sb / k:15.3f}")
    prev = cur
