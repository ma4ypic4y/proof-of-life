#!/usr/bin/env python3
"""Turn the clean serial rebuild log (verify.log from the Mac mini) into verify_report.json."""
import json, os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
log = open(sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "logs/verify.log")).read().splitlines()
mods = {}; fails = []; total = None
for line in log:
    m = re.match(r"OK\s+(\S+) (\d+)s", line)
    if m and m.group(1) != "Atlas(all)": mods[m.group(1)] = int(m.group(2))
    if line.startswith("FAIL"): fails.append(line.split()[1])
    m = re.match(r"TOTAL (\d+)s", line)
    if m: total = int(m.group(1))
rep = {"host": "Mac mini (Apple M4), from an empty .lake, one lake build per module (the six birth-certificate modules were built together as dependencies)",
       "modules": len(mods) + len(fails), "modules_ok": len(mods), "failed": fails,
       "total_seconds": total if total is not None else sum(mods.values()),
       "atlas_ok": any(l.startswith("OK   Atlas(all)") for l in log), "module_seconds": mods}
json.dump(rep, open(os.path.join(here, "verify_report.json"), "w"), indent=1)
print({k: v for k, v in rep.items() if k != "module_seconds"})
