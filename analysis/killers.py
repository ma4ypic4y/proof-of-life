#!/usr/bin/env python3
"""For every organism the abstract run cannot certify, measure how often its code
survives a random partner and find an explicit partner that kills it.

Expected child E: the reversed genome (paper's rule) or the genome (other rule).
A partner kills the organism when the child does not carry E's instruction bytes
at E's instruction positions. The killer is searched among random partners,
then among partners that zero or set the byte the abstract run got stuck on.
Also records one partner the organism survives. Writes data/killers.json.
"""
import json, os, random, sys
sys.path.insert(0, os.path.dirname(__file__))
from bff import run

ROOT = os.path.join(os.path.dirname(__file__), "..")
ab = {x["id"]: x for x in json.load(open(os.path.join(ROOT, "data/abstract.json")))}
orgs = json.load(open(os.path.join(ROOT, "data/classify.json")))
OPS = b"<>{}+-.,[]"
out = []
for o in orgs:
    a = ab[o["id"]]
    if a["abstract_ok"]:
        continue
    heads = o["rule"] == "heads"
    P = bytes.fromhex(o["genome"])
    E = P if heads else P[::-1]
    code = [i for i in range(64) if E[i] in OPS]
    def child(B):
        t = bytearray(P + B); run(t, heads=heads); return bytes(t[64:])
    def survives(B):
        c = child(B); return all(c[i] == E[i] for i in code)
    rng = random.Random(1234)
    trials = [bytes(rng.randrange(256) for _ in range(64)) for _ in range(2000)]
    alive = [survives(B) for B in trials]
    rate = sum(alive) / len(alive)
    killer = next((B for B, ok in zip(trials, alive) if not ok), None)
    if killer is None:  # targeted: vary the byte the abstract run stumbled on
        k = a["at"] - 64 if a["at"] >= 64 else None
        for base in trials[:200]:
            for v in (0, 1, 91, 93, 255):
                if k is None: break
                B = bytearray(base); B[k] = v; B = bytes(B)
                if not survives(B): killer = B; break
            if killer: break
    saver = next((B for B, ok in zip(trials, alive) if ok), None)
    rec = {"id": o["id"], "rule": o["rule"], "genome": o["genome"], "survival": round(rate, 4),
           "stuck_step": a["step"], "stuck_reason": a["reason"], "stuck_at": a["at"],
           "killer": killer.hex() if killer else None, "saver": saver.hex() if saver else None}
    if killer:
        c = child(killer); rec["killer_child"] = c.hex()
        rec["code_lost"] = sum(c[i] != E[i] for i in code); rec["code_total"] = len(code)
    out.append(rec)
    print(f"{o['id']:11s} {o['rule']:8s} survives {100*rate:5.1f}% of random partners; killer found: {killer is not None}"
          + (f", loses {rec['code_lost']}/{rec['code_total']} code bytes" if killer else "") + f"; saver found: {saver is not None}")
json.dump(out, open(os.path.join(ROOT, "data/killers.json"), "w"), indent=1)
