"""Generate test vectors for the Lean interpreter from the Python reference.

Each line of test_vectors.txt is 512 hex chars: the 128-byte input tape followed
by the 128-byte tape that analysis/bff.py `run` (8192 steps, no heads) leaves.
Run from this directory:  python3 gen_vectors.py
"""
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "analysis"))
import bff  # noqa: E402

atlas = json.load(open(os.path.join(ROOT, "web", "data", "atlas.json")))
P = bytes.fromhex([x for x in atlas["noheads"] if x["seed"] == 30][0]["rep"])

rng = random.Random(12345)
OPS = b"<>{}+-.,[]"
cases = []
for _ in range(20):  # the replicator against random partners
    cases.append(bytearray(P) + bytearray(rng.randrange(256) for _ in range(64)))
for _ in range(40):  # uniformly random tapes
    cases.append(bytearray(rng.randrange(256) for _ in range(128)))
for dens in (0.3, 0.6, 0.9):  # opcode-dense tapes: wraps, scans, all halts
    for _ in range(60):
        t = bytearray()
        for _ in range(128):
            r = rng.random()
            if r < dens:
                t.append(rng.choice(OPS))
            elif r < dens + 0.05:
                t.append(0)
            else:
                t.append(rng.randrange(256))
        cases.append(t)

for heads, fn in [(False, "test_vectors.txt"), (True, "test_vectors_heads.txt")]:
    lines = []
    for c in cases:
        t = bytearray(c)
        bff.run(t, heads=heads)
        lines.append(bytes(c).hex() + bytes(t).hex())
    with open(os.path.join(HERE, fn), "w") as f:
        f.write("\n".join(lines) + "\n")
    print(len(lines), "vectors written to", fn)
