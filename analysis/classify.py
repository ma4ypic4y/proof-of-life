#!/usr/bin/env python3
"""Classify every organism for formal verification.

For each winning genome P (both rules) plus the paper's Figure 4 specimen, run
it against 400 random partners and ask:
  exact-universal   : the child half is always the same string C (C = rev P for
                      mirror copiers, C = P for forward copiers) and P survives
  child-constant    : the child is partner-independent but differs from P/rev P;
                      then check whether C itself is exact-universal (a one-
                      generation precursor)
  partner-dependent : the child varies with the partner; keep a witness pair
Writes data/classify.json (consumed by the Lean generator and the page).
"""
import json, os, random, sys
sys.path.insert(0, os.path.dirname(__file__))
from bff import run, show

ROOT = os.path.join(os.path.dirname(__file__), "..")
atlas = json.load(open(os.path.join(ROOT, "web/data/atlas.json")))
rng = random.Random(7)
PARTNERS = [bytes(rng.randrange(256) for _ in range(64)) for _ in range(400)] + [bytes([v]) * 64 for v in (0, 255, 91, 93)]


def children(P, heads):
    out = []
    for B in PARTNERS:
        t = bytearray(P + B)
        run(t, heads=heads)
        out.append((bytes(t[:64]), bytes(t[64:])))
    return out


def classify(P, heads):
    ch = children(P, heads)
    parents_ok = all(a == P for a, _ in ch)
    kids = {c for _, c in ch}
    if len(kids) == 1:
        C = next(iter(kids))
        if C == P[::-1] and parents_ok: return {"class": "exact-mirror"}
        if C == P and parents_ok: return {"class": "exact-forward"}
        # partner-independent child: is it itself an exact replicator?
        sub = classify(C, heads) if C not in (P, P[::-1]) else {"class": "?"}
        return {"class": "child-constant", "child": C.hex(), "child_class": sub["class"], "parent_intact": parents_ok}
    # which partner makes it differ from the majority child?
    from collections import Counter
    common, n = Counter(c for _, c in ch).most_common(1)[0]
    bad = next(B for B, (_, c) in zip(PARTNERS, ch) if c != common)
    return {"class": "partner-dependent", "majority": n, "of": len(ch), "majority_child": common.hex(), "witness": bad.hex()}


orgs = []
paper = b"[[{.>]-]" + b" " * 48 + b"]-]>.{[["
orgs.append({"id": "paper-fig4", "rule": "noheads", "genome": paper.hex(), **classify(paper, False)})
for key, heads in (("noheads", False), ("heads", True)):
    for w in atlas[key]:
        if "rep" not in w: continue
        P = bytes.fromhex(w["rep"])
        r = {"id": f"world-{w['seed']}", "rule": key, "genome": w["rep"], **classify(P, heads)}
        if not heads and r["class"] == "exact-mirror":
            # closed lineage needs the mirror strand to be an exact mirror copier too
            r["mirror_strand"] = classify(P[::-1], heads)["class"]
        orgs.append(r)
json.dump(orgs, open(os.path.join(ROOT, "data/classify.json"), "w"), indent=1)
from collections import Counter
print(Counter((o["rule"], o["class"], o.get("child_class", ""), o.get("mirror_strand", "")) for o in orgs))
for o in orgs:
    if o["class"] not in ("exact-mirror", "exact-forward"):
        print(o["id"], o["rule"], o["class"], o.get("child_class", ""), o.get("majority", ""), o.get("of", ""))
