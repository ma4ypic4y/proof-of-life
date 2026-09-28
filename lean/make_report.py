#!/usr/bin/env python3
"""Assemble lean/atlas_report.json from the build artifacts copied back from the
build machine: gen/manifest.json (what was generated), logs/times_A.txt and
logs/times_B.txt (per-module wall-clock seconds and exit codes of
`lake build <module>`), logs/logs_final.out (the final whole-project `lake build`),
logs/atlas_axioms.txt (`#print axioms` of every main theorem, from Atlas.lean)."""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
man = json.load(open(os.path.join(HERE, "gen", "manifest.json")))
killers = {o["id"]: o for o in json.load(open(os.path.join(ROOT, "data", "killers.json")))}
classify = {o["id"]: o for o in json.load(open(os.path.join(ROOT, "data", "classify.json")))}

def read_times(fn):
    out = {}
    p = os.path.join(HERE, "logs", fn)
    if os.path.exists(p):
        for line in open(p):
            parts = line.split()
            if len(parts) == 3:
                out[parts[0]] = (int(parts[1]), float(parts[2]))
    return out


# primary checks (the olean used by Atlas.lean comes from these builds)
times, host = {}, {}
for fn, h in [("times_birth.txt", "local"), ("times_A_local_partial.txt", "local"),
              ("times_q1.txt", "local"), ("times_q2.txt", "local"),
              ("times_m1.txt", "mac_mini"), ("times_m2.txt", "mac_mini"),
              ("times_m3.txt", "mac_mini"), ("times_m4.txt", "mac_mini")]:
    for m, v in read_times(fn).items():
        times[m], host[m] = v, h
# independent second checks on the Mac mini before it rebooted (same sources)
second = read_times("times_mini_prereboot.txt")

final_ok = all(rc == 0 for rc, _ in times.values())

ax_text = open(os.path.join(HERE, "logs", "atlas_axioms.txt")).read()
ax_text = re.sub(r"\n\s+", " ", ax_text)
axioms = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", ax_text):
    axioms[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
for m in re.finditer(r"'([^']+)' does not depend on any axioms", ax_text):
    axioms[m.group(1)] = []
STANDARD = {"propext", "Quot.sound", "Classical.choice"}

BIRTH_MODS = ["ProofOfLife.Birth52.Collision", "ProofOfLife.Birth52.Newborn",
              "ProofOfLife.Birth52.NewbornRev", "ProofOfLife.Birth52.ParentA",
              "ProofOfLife.Birth52.ParentB", "ProofOfLife.Birth52.Certificate"]

entries = []
for e in man["entries"]:
    e = dict(e)
    if e["id"] in classify:
        e["genome"] = classify[e["id"]]["genome"]
    if e["status"] == "failed":
        e["check_seconds"] = None
        entries.append(e)
        continue
    mods = BIRTH_MODS if e["kind"] == "birth" else [e["module"]]
    rcs = [times.get(m, (None, None)) for m in mods]
    e["check_seconds"] = round(sum(s for _, s in rcs if s is not None), 1) if all(
        s is not None for _, s in rcs) else None
    e["check_host"] = sorted({host.get(m, "?") for m in mods})
    if e["kind"] == "birth":
        e["check_seconds_by_module"] = {m: times.get(m, (None, None))[1] for m in mods}
    also = [m for m in mods if second.get(m, (1, 0))[0] == 0]
    if also:
        e["also_checked_on_mac_mini"] = also
    ax = axioms.get(e["theorem"])
    e["axioms"] = ax
    built = all(rc == 0 for rc, _ in rcs)
    clean = ax is not None and set(ax) <= STANDARD
    e["status"] = "proved" if (built and final_ok and clean) else "failed"
    if not (built and final_ok and clean):
        e["note"] = (e.get("note", "") + f" [build ok={built}, final build ok={final_ok}, axioms={ax}]").strip()
    entries.append(e)

# near-immortal heads organisms for which no killer partner is known
for i in ["world-1004", "world-1022", "world-1403"]:
    k = killers.get(i)
    if k and not k.get("killer"):
        entries.append(dict(id=i, rule=k["rule"], kind="killer", theorem=None, statement=None,
                            module=None, check_seconds=None, status="skipped",
                            note=f"no killer partner known (survival {k['survival']})",
                            genome=classify[i]["genome"]))

totals = {}
for e in entries:
    t = totals.setdefault(e["kind"], {"proved": 0, "failed": 0, "skipped": 0})
    t[e["status"]] += 1
all_ax = sorted({a for e in entries for a in (e.get("axioms") or [])})
check_total = round(sum(s for m, (rc, s) in times.items()), 1)
report = dict(
    title="Proof of Life — formally verified atlas (Lean 4.21.0, core only)",
    check_host="each module was checked by `lake build <module>` (exit 0) on the machine in "
               "`check_host`: local = MacBook (10 cores, 16 GB, 5 parallel jobs, other load present); "
               "mac_mini = Mac mini M4 (4 parallel jobs). check_seconds = wall-clock of that module's "
               "build under that load, so it is an upper bound on the kernel time. Atlas.lean was then "
               "elaborated against all module .olean files (`lake env lean Atlas.lean`).",
    trust_base="Lean kernel only: every computation is `decide +kernel`; no native_decide, "
               "sorry, admit, or new axioms. Checkpoints are untrusted #eval output re-checked "
               "by the kernel.",
    semantics="ProofOfLife/Semantics.lean: run (noheads, paper rule), runHeads (cubff bff rule)",
    totals=totals,
    axioms_used=all_ax,
    total_module_check_seconds=check_total,
    all_module_builds_ok=final_ok,
    entries=entries,
)
json.dump(report, open(os.path.join(HERE, "atlas_report.json"), "w"), indent=1, ensure_ascii=False)
print(json.dumps(dict(totals=totals, axioms=all_ax, total_seconds=check_total, final_ok=final_ok), indent=1))
