#!/usr/bin/env python3
"""Print the markdown tables used in REPORT.md, straight from the data files."""
import json, os
ROOT = os.path.join(os.path.dirname(__file__), "..")
J = lambda p: json.load(open(os.path.join(ROOT, p)))
atlas, ab, kl, lean = J("web/data/atlas.json"), {x["id"]: x for x in J("data/abstract.json")}, {x["id"]: x for x in J("data/killers.json")}, J("lean/atlas_report.json")
geo = J("web/data/copygeo.json"); U = J("web/data/universal.json")
cert = {}
for e in lean["entries"]:
    cert.setdefault(e["id"], {})[e["kind"]] = e["status"]
def verdict(i):
    c = cert.get(i, {})
    if c.get("exact") == "proved": return "∀ partners" + (" + lineage" if c.get("lineage") == "proved" else "")
    if c.get("achilles") == "proved": return "∀ partners with byte 63 ≠ 0"
    if c.get("killer") == "proved": return "killer partner"
    return "—"
print("### Paper's rule (heads start at 0)\n")
print("| world | alive at epoch | copies | exact mirror | + / − in top 16 | any-partner test | Lean |")
print("|---|---:|---|---|---:|---:|---|")
for w in atlas["noheads"]:
    if "rep" not in w: continue
    i = f"world-{w['seed']}"; back = w["rev"] > w["fwd"]
    u = U.get(str(w["seed"])); ut = f"{u[0]}/{u[1]}" if u and w["mirror"] > w["shift"] + w["other"] else "—"
    print(f"| {w['seed']} | {w['t']:,} | {'backwards' if back else 'forwards'} | {'yes' if w['mirror'] > w['shift'] + w['other'] else 'no'} | {w['rep_count']} / {w['rev_count']} | {ut} | {verdict(i)} |")
print(f"| paper Fig. 4 | — | backwards | yes | — | — | {verdict('paper-fig4')} |")
print("\n### Genome-set heads (cubff `bff`)\n")
print("| world | alive at epoch | copies | random partners that receive its code at the same positions | Lean |")
print("|---|---:|---|---:|---|")
for w in atlas["heads"]:
    if "rep" not in w: continue
    i = f"world-{w['seed']}"; k = kl.get(i)
    surv = "100% (exact)" if ab[i]["abstract_ok"] else (f"{100 * k['survival']:.1f}%" if k else "—")
    print(f"| {w['seed']} | {w['t']:,} | {'backwards' if w['rev'] > w['fwd'] else 'forwards'} | {surv} | {verdict(i)} |")
print("\n### Copy direction across whole soups\n")
print("| soups | rule | copy steps | backwards |")
print("|---|---|---:|---:|")
for k, lab in (("control-noheads", "random, before life"), ("control-heads", "random, before life"), ("alive-noheads", "living"), ("alive-heads", "living")):
    v = geo[k]; n = v["rev"] + v["fwd"]
    print(f"| {lab} ({v['soups']}) | {'heads start at 0' if 'noheads' in k else 'genome-set heads'} | {n:,} | {100 * v['rev'] / n:.2f}% |")
t = lean["totals"]
print("\n### Lean certificates\n")
print("| kind | proved | failed | skipped |\n|---|---:|---:|---:|")
for k in ("birth", "exact", "lineage", "achilles", "killer"):
    print(f"| {k} | {t[k]['proved']} | {t[k]['failed']} | {t[k]['skipped']} |")
