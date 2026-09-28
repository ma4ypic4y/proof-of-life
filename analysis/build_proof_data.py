#!/usr/bin/env python3
"""Data for the Proof of Life page: organisms, Python abstract-run results,
killer partners, and (when present) the Lean atlas report, which is the only
source of 'proved' statuses. Writes web/data/proof.json."""
import json, os

ROOT = os.path.join(os.path.dirname(__file__), "..")
cls = {o["id"]: o for o in json.load(open(os.path.join(ROOT, "data/classify.json")))}
ab = {o["id"]: o for o in json.load(open(os.path.join(ROOT, "data/abstract.json")))}
kl = {o["id"]: o for o in json.load(open(os.path.join(ROOT, "data/killers.json")))}
atlas = json.load(open(os.path.join(ROOT, "web/data/atlas.json")))
alive_epoch = {f"world-{w['seed']}": w["t"] for k in ("noheads", "heads") for w in atlas[k]}
report_path = os.path.join(ROOT, "lean/atlas_report.json")
report = json.load(open(report_path)) if os.path.exists(report_path) else None
verify_path = os.path.join(ROOT, "lean/verify_report.json")
if report is not None and os.path.exists(verify_path):
    report["verify"] = json.load(open(verify_path))
orgs = []
for oid, c in cls.items():
    a = ab[oid]
    rec = {"id": oid, "rule": c["rule"], "genome": c["genome"], "alive_epoch": alive_epoch.get(oid),
           "abstract_ok": a["abstract_ok"], "child": "mirror" if a.get("child_is_mirror") else "copy" if a.get("child_is_copy") else None}
    if not a["abstract_ok"]:
        rec.update(stuck_step=a["step"], stuck_reason=a["reason"], stuck_at=a["at"])
    if oid in kl:
        k = kl[oid]
        rec.update(survival=k["survival"], killer=k["killer"])
    orgs.append(rec)
birth = None
bp = os.path.join(ROOT, "data/birth52.json")
if os.path.exists(bp):
    b = json.load(open(bp)); r = b["births"][0]
    li = json.load(open(os.path.join(ROOT, "data/birth52_lean_inputs.json")))
    import csv
    film = [(int(x["epoch"]), int(x["plus"]) + int(x["minus"])) for x in csv.DictReader(open(os.path.join(ROOT, "data/film52b/stats.csv")))]
    first = next(e for e, c in film if c > 0)
    k90 = next((e, c) for e, c in film if c >= 90000)
    birth = {"seed": b["seed"], "epoch_index": b["epoch_index"], "pair": r["pair_index"], "pairs_total": 65536,
             "left_slot": r["left_slot"], "right_slot": r["right_slot"], "mutations": len(r["mutations"]),
             "A": li["A"], "B": li["B"], "A_out": li["A_out"], "C": li["C"], "killer_A": li["killer_A"], "killer_B": li["killer_B"],
             "matches_saved_soup": r["matches_saved_soup"], "first_epoch": first, "epochs_to_90k": k90[0] - first, "count_90k": k90[1]}
json.dump({"organisms": orgs, "lean": report, "birth": birth}, open(os.path.join(ROOT, "web/data/proof.json"), "w"), separators=(",", ":"))
print(len(orgs), "organisms;", "lean report present" if report else "no lean report yet")
