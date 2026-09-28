#!/usr/bin/env python3
"""Experiment 1 — the atlas of origins.

Many independent worlds under the paper's canonical setup (bff_noheads,
2^17 programs of 64 bytes, mutation 1/4096 per byte per interaction,
8192-step limit), each run for at most 16,384 epochs. A world "comes alive"
when its high-order entropy (Shannon entropy minus brotli bits/byte, as in
cubff) first exceeds 3.0 bits. Living worlds run 256 more epochs so the
winning replicator dominates, then we record a census of the soup.

usage: atlas.py <first_seed> <last_seed> <outdir> [--jobs 10] [extra tol args]
"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

first, last, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
jobs = 10
extra = sys.argv[4:]
if extra[:1] == ["--jobs"]:
    jobs, extra = int(extra[1]), extra[2:]
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
TOL = os.environ.get("TOL", os.path.join(ROOT, "engine", "tol"))  # build it first: see README
for d in ("logs", "census", "results", "final"):
    os.makedirs(os.path.join(out, d), exist_ok=True)

def run(seed):
    res = os.path.join(out, "results", f"{seed}.json")
    if os.path.exists(res):
        return
    cmd = [TOL, "--seed", str(seed), "--max-epochs", "16384", "--log-every", "16",
           "--log", os.path.join(out, "logs", f"{seed}.csv"), "--tail", "256",
           "--census", os.path.join(out, "census", f"{seed}.jsonl"),
           "--save-final", os.path.join(out, "final", f"{seed}.dat"),
           "--result", res + ".tmp"] + extra
    subprocess.run(cmd, stdout=subprocess.DEVNULL, check=True)
    os.rename(res + ".tmp", res)

with ThreadPoolExecutor(jobs) as ex:
    list(ex.map(run, range(first, last + 1)))
