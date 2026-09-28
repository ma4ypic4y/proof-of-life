#!/usr/bin/env python3
"""Atlas report: outcome of every world, and anatomy of every origin of life.

usage: atlas_report.py <atlas_dir> [--heads] [--json out.json]
"""
import glob, json, os, random, sys

sys.path.insert(0, os.path.dirname(__file__))
from bff import copy_geometry, mirror_skeleton, offspring_identity, show, OPS

atlas = sys.argv[1]
heads = "--heads" in sys.argv
out_json = sys.argv[sys.argv.index("--json") + 1] if "--json" in sys.argv else None

worlds = []
for f in sorted(glob.glob(os.path.join(atlas, "results", "*.json")),
                key=lambda x: int(os.path.basename(x)[:-5])):
    r = json.load(open(f))
    if r.get("skip"):
        continue  # seeds deliberately not run (the canonical atlas was capped)
    w = {"seed": r["seed"], "transition": r["transition"], "end": r["end"]}
    if r["transition"] >= 0:
        c = [json.loads(l) for l in open(os.path.join(atlas, "census", f"{r['seed']}.jsonl"))][-1]
        top = c["top"]
        w["distinct"] = c["distinct"]
        w["top"] = top
        reps = [t for t in top if t["selfrep"] >= 5]  # cubff's kSelfrepThreshold
        w["outcome"] = "life" if reps else "crystal"
        if reps:
            p = bytes.fromhex(reps[0]["hex"])
            hexes = {t["hex"]: t["count"] for t in top}
            w["rep"] = reps[0]["hex"]
            w["rep_count"] = reps[0]["count"]
            w["rev_count"] = hexes.get(bytes(reversed(p)).hex(), 0)
            w["mirror_skeleton"] = mirror_skeleton(p)
            w["geometry"] = copy_geometry(p, heads=heads)
            w["child_fwd"], w["child_rev"] = offspring_identity(p, heads=heads)
            w["n_ops"] = sum(b in OPS for b in p)
    else:
        w["outcome"] = "none"
    worlds.append(w)

n = len(worlds)
by = {k: [w for w in worlds if w["outcome"] == k] for k in ("life", "crystal", "none")}
print(f"worlds: {n}  life: {len(by['life'])}  crystal: {len(by['crystal'])}  none: {len(by['none'])}"
      f"  (transition by entropy: {sum(w['transition'] >= 0 for w in worlds)}/{n})")
for w in by["life"]:
    g = w["geometry"]
    print(f"seed {w['seed']:5d} T*={w['transition']:6d} ops={w['n_ops']:2d} mirror_skel={w['mirror_skeleton']:.2f} "
          f"copies mirror/shift/other={g['mirror']}/{g['shift']}/{g['other']} "
          f"child=fwd {w['child_fwd']:.2f} rev {w['child_rev']:.2f}  rev-in-top16={w['rev_count']}/{w['rep_count']}")
    print("      " + show(bytes.fromhex(w["rep"])))
for w in by["crystal"]:
    print(f"seed {w['seed']:5d} T*={w['transition']:6d} CRYSTAL  top: {show(bytes.fromhex(w['top'][0]['hex']))} x{w['top'][0]['count']}")

# Null model for the skeleton mirror score: random 64-byte programs with the
# same instruction count as the observed replicators.
rng = random.Random(0)
null = []
for w in by["life"]:
    for _ in range(200):
        p = bytearray(rng.randrange(256) for _ in range(64))
        ops = [ord(c) for c in "<>{}+-.,[]"]
        for i in rng.sample(range(64), w["n_ops"]):
            p[i] = rng.choice(ops)
        null.append(mirror_skeleton(bytes(p)))
if by["life"]:
    obs = sum(w["mirror_skeleton"] for w in by["life"]) / len(by["life"])
    print(f"mean mirror-skeleton score: observed {obs:.2f}  vs null {sum(null) / len(null):.3f}")
if out_json:
    json.dump(worlds, open(out_json, "w"))
