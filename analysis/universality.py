#!/usr/bin/env python3
"""Does each evolved replicator copy itself into *any* partner?

For every replicator in web/data/atlas.json, run it against 1,500 uniformly
random partners, 500 partners made only of instruction bytes (the most
disruptive case), and the 12 constant partners (all 0x00, all 0xFF, all '[' ...).
Success = the partner half ends exactly equal to the expected child (the
reversed genome for mirror copiers, the genome itself for forward copiers)
and the parent half is unchanged. Writes web/data/universal.json.
"""
import json, os, random, sys
sys.path.insert(0, os.path.dirname(__file__))
from bff import run

ROOT = os.path.join(os.path.dirname(__file__), "..")
d = json.load(open(os.path.join(ROOT, "web/data/atlas.json")))
rng = random.Random(11)
OPS = b"<>{}+-.,[]"
partners = ([bytes(rng.randrange(256) for _ in range(64)) for _ in range(1500)]
            + [bytes(rng.choice(OPS) for _ in range(64)) for _ in range(500)]
            + [bytes([v]) * 64 for v in (0, 255, *OPS)])
out = {}
for key, heads in (("noheads", False), ("heads", True)):
    for w in d[key]:
        if "rep" not in w:
            continue
        p = bytes.fromhex(w["rep"])
        mirror = w["mirror"] > w["shift"] + w["other"]
        child = bytes(reversed(p)) if mirror else p
        ok = 0
        for b in partners:
            t = bytearray(p + b)
            run(t, heads=heads)
            ok += bytes(t[64:]) == child and bytes(t[:64]) == p
        out[str(w["seed"])] = [ok, len(partners)]
        print(key, w["seed"], "mirror" if mirror else "forward", f"{ok}/{len(partners)}")
json.dump(out, open(os.path.join(ROOT, "web/data/universal.json"), "w"))
