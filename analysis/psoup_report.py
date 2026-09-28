#!/usr/bin/env python3
"""Prompt-soup report -> web/data/psoup.json

For every world of a prompt-soup run, per epoch:
  * confusion: share of texts that are the model saying it does not understand
    ("sorry", "could you clarify", "provide more context", ...);
  * copy / persist / novel: how each rewritten slot relates to the two texts
    that produced it (see psoup_events.py);
  * biggest lineage: size of the largest cluster of near-identical texts
    (character 5-gram Jaccard >= 0.5 to the cluster's first member).
Also keeps text snapshots of one world for the page's slider.

usage: psoup_report.py <run_dir> [--show-world w1] [--every 2] [--control <run_dir>]
"""
import glob, gzip, json, os, re, sys

run = sys.argv[1]
show = sys.argv[sys.argv.index("--show-world") + 1] if "--show-world" in sys.argv else None
every = int(sys.argv[sys.argv.index("--every") + 1]) if "--every" in sys.argv else 2
control = sys.argv[sys.argv.index("--control") + 1] if "--control" in sys.argv else None

CONFUSED = re.compile(r"sorry|apologi|not sure what|unclear|could you (please )?(clarify|provide)|"
                      r"provide (more|some|additional) (context|details|information)|don't understand|"
                      r"do not understand|not able to understand|seems like (you|there)|appears to be a (list|collection|mix|random)|"
                      r"random (words|string|collection)|unrelated words", re.I)


def grams(s, k=5):
    s = s.lower()
    return frozenset(s[i:i + k] for i in range(max(1, len(s) - k + 1)))


def jac(a, b):
    return len(a & b) / max(1, len(a | b))


def clusters(texts, thr=0.5):
    reps, sizes, label = [], [], []
    for t in texts:
        g = grams(t)
        for ci, r in enumerate(reps):
            if jac(g, r) >= thr:
                sizes[ci] += 1
                label.append(ci)
                break
        else:
            reps.append(g)
            sizes.append(1)
            label.append(len(reps) - 1)
    return sizes, label


out = {"worlds": [], "control": []}
jobs = [(w, "worlds") for w in sorted(glob.glob(os.path.join(run, "w*")))]
if control:
    jobs += [(w, "control") for w in sorted(glob.glob(os.path.join(control, "w*")))]
for wdir, dest in jobs:
    path = os.path.join(wdir, "soup.jsonl")
    fh = open(path) if os.path.exists(path) else gzip.open(path + ".gz", "rt")
    rows = [json.loads(l) for l in fh]
    w = {"name": os.path.basename(wdir), "epoch": [], "confused": [], "copy": [], "persist": [], "novel": [],
         "biggest": [], "distinct": []}
    prev = None
    for r in rows:
        texts = r["texts"]
        n = len(texts)
        w["epoch"].append(r["epoch"])
        w["confused"].append(round(sum(bool(CONFUSED.search(t)) for t in texts) / n, 3))
        sizes, _ = clusters(texts)
        w["biggest"].append(max(sizes))
        w["distinct"].append(len(sizes))
        if prev is not None and "pairs" in r:
            c = p = nv = 0
            for a, b in r["pairs"]:
                ga, gb, gn = grams(prev[a]), grams(prev[b]), grams(texts[b])
                sa, sb = jac(gn, ga), jac(gn, gb)
                if sa > sb and sa >= 0.3: c += 1
                elif sb >= sa and sb >= 0.3: p += 1
                else: nv += 1
            k = len(r["pairs"])
            w["copy"].append(round(c / k, 3)); w["persist"].append(round(p / k, 3)); w["novel"].append(round(nv / k, 3))
        else:
            w["copy"].append(None); w["persist"].append(None); w["novel"].append(None)
        prev = texts
    if dest == "worlds" and (show is None or w["name"] == show):
        snaps = []
        for r in rows:
            if r["epoch"] % every == 0:
                _, label = clusters(r["texts"])
                snaps.append({"epoch": r["epoch"], "texts": r["texts"], "cluster": label})
        w["snaps"] = snaps
    out[dest].append(w)
    last = w["epoch"][-1]
    print(f"{dest} {w['name']}: epochs 0..{last}  confused max {max(w['confused']):.2f} at epoch "
          f"{w['epoch'][w['confused'].index(max(w['confused']))]}, final {w['confused'][-1]:.2f}; "
          f"persist final {w['persist'][-1]}; copy final {w['copy'][-1]}; biggest lineage final {w['biggest'][-1]}")

dst = os.path.join(os.path.dirname(__file__), "..", "web", "data", "psoup.json")
json.dump(out, open(dst, "w"), separators=(",", ":"))
print("wrote", dst, os.path.getsize(dst), "bytes")
