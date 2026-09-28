#!/usr/bin/env python3
"""Build web/data/atlas.json from the atlas runs (both head rules)."""
import csv, glob, json, os, sys

sys.path.insert(0, os.path.dirname(__file__))
from bff import copy_geometry, copy_positions, mirror_skeleton, offspring_identity, OPS

ROOT = os.path.join(os.path.dirname(__file__), "..")


def world_rows(atlas, heads):
    out = []
    for f in sorted(glob.glob(os.path.join(atlas, "results", "*.json")),
                    key=lambda x: int(os.path.basename(x)[:-5])):
        r = json.load(open(f))
        if r.get("skip"):
            continue  # seeds deliberately not run (the canonical atlas was capped)
        w = {"seed": r["seed"], "t": r["transition"], "end": r["end"]}
        # entropy trace, every 64 epochs, 2 decimals
        trace = []
        with open(os.path.join(atlas, "logs", f"{r['seed']}.csv")) as lf:
            for row in csv.DictReader(lf):
                e = int(row["epoch"])
                if (e - 1) % 64 == 0:
                    trace.append(round(float(row["higher_entropy"]), 2))
        w["trace"] = trace
        if r["transition"] >= 0:
            c = [json.loads(l) for l in open(os.path.join(atlas, "census", f"{r['seed']}.jsonl"))][-1]
            reps = [t for t in c["top"] if t["selfrep"] >= 5]
            w["distinct"] = c["distinct"]
            w["top"] = [[t["hex"], t["count"], t["selfrep"]] for t in c["top"]]
            if reps:
                p = bytes.fromhex(reps[0]["hex"])
                g = copy_geometry(p, heads=heads)
                fwd, rev = offspring_identity(p, heads=heads)
                counts = {t["hex"]: t["count"] for t in c["top"]}
                w.update(rep=reps[0]["hex"], rep_count=reps[0]["count"],
                         rev_count=counts.get(bytes(reversed(p)).hex(), 0),
                         mirror=g["mirror"], shift=g["shift"], other=g["other"], rev=g["rev"], fwd=g["fwd"],
                         child_fwd=round(fwd, 3), child_rev=round(rev, 3),
                         skel=round(mirror_skeleton(p), 3), ops=sum(b in OPS for b in p),
                         mach=copy_positions(p, heads=heads),
                         mach_rev=sorted(63 - x for x in copy_positions(bytes(reversed(p)), heads=heads)))
        out.append(w)
    return out


data = {"noheads": world_rows(os.path.join(ROOT, "data/atlas"), False),
        "heads": world_rows(os.path.join(ROOT, "data/atlas_heads"), True)}
os.makedirs(os.path.join(ROOT, "web/data"), exist_ok=True)
json.dump(data, open(os.path.join(ROOT, "web/data/atlas.json"), "w"), separators=(",", ":"))
for k, ws in data.items():
    alive = [w for w in ws if w["t"] >= 0]
    reps = [w for w in alive if "rep" in w]
    mirror = [w for w in reps if w["mirror"] > w["shift"] + w["other"]]
    print(f"{k}: worlds {len(ws)}, entropy-transition {len(alive)}, replicator {len(reps)}, "
          f"mirror-copying {len(mirror)}, palindromes {sum(w['skel'] >= 0.9 for w in reps)}, "
          f"rev strand present {sum(w['rev_count'] > 0 for w in reps)}")
print("bytes:", os.path.getsize(os.path.join(ROOT, "web/data/atlas.json")))
