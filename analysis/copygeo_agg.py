#!/usr/bin/env python3
"""Aggregate engine/copygeo output (data/copygeo.jsonl) into web/data/copygeo.json."""
import json, os
from collections import defaultdict

ROOT = os.path.join(os.path.dirname(__file__), "..")
out = defaultdict(lambda: {"soups": 0, "pairs": 0, "cross": 0, "rev": 0, "fwd": 0, "per": []})
for line in open(os.path.join(ROOT, "data/copygeo.jsonl")):
    d = json.loads(line)
    assert d["trace_mismatches"] == 0, d  # traced interpreter must agree with the engine
    o = out[d["set"]]
    o["soups"] += 1; o["pairs"] += d["pairs"]; o["cross"] += d["cross_copies"]
    o["rev"] += d["reversed"]; o["fwd"] += d["forward"]
    if d["reversed"] + d["forward"]:
        o["per"].append(round(d["reversed"] / (d["reversed"] + d["forward"]), 4))
json.dump(out, open(os.path.join(ROOT, "web/data/copygeo.json"), "w"), separators=(",", ":"))
for k, v in out.items():
    n = v["rev"] + v["fwd"]
    print(f"{k:16s} soups {v['soups']:3d}  directional steps {n:10,d}  backwards {100 * v['rev'] / max(1, n):6.2f}%")
