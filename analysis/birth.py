#!/usr/bin/env python3
"""Birth certificate: the collision in which world 52's lineage first appears.

Loads the soup before and after epoch 5857 (0-based; the soup after it has 5858
epochs done), finds the first program carrying the winning genome's code,
recomputes that epoch's pairing and mutations with cubff's SplitMix64 streams,
re-runs the one collision that produced it, and checks the result against the
saved soup byte for byte. Then classifies parents and children.

usage: birth.py <snap_before.dat> <snap_after.dat> <genome_hex> <seed> <epoch_index> > data/birth52.json
"""
import json, os, struct, sys
sys.path.insert(0, os.path.dirname(__file__))
from bff import run, show
from abstract import arun

M64 = (1 << 64) - 1


def sm64(s):
    z = (s + 0x9E3779B97F4A7C15) & M64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M64
    return z ^ (z >> 31)


def load(p):
    d = open(p, "rb").read()
    _, n, ep = struct.unpack("<QQQ", d[:24])
    return n, ep, d[24:]


before, after, ghex, seed, epoch = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
n, ep0, s0 = load(before)
_, ep1, s1 = load(after)
assert ep0 == epoch and ep1 == epoch + 1, (ep0, ep1)
G = bytes.fromhex(ghex); R = G[::-1]
OPS = set(b"<>{}+-.,[]")
ip = [i for i in range(64) if G[i] in OPS]; ir = [i for i in range(64) if R[i] in OPS]


def lineage(q):
    a = sum(q[i] == G[i] for i in ip) / len(ip); b = sum(q[i] == R[i] for i in ir) / len(ir)
    return "+" if a >= 0.8 and a >= b else "-" if b >= 0.8 else None


prog = lambda s, i: s[i * 64:(i + 1) * 64]
born = [i for i in range(n) if lineage(prog(s1, i))]
before_hits = [i for i in range(n) if lineage(prog(s0, i))]
seedf = lambda x: sm64(sm64(seed) ^ sm64(x))
perm = list(range(n))
for i in range(n - 1, -1, -1):
    j = sm64(seedf((epoch * n + i) & M64)) % (i + 1)
    perm[i], perm[j] = perm[j], perm[i]
where = {perm[k]: k // 2 for k in range(n)}
es = seedf(epoch)
records = []
for slot in born:
    k = where[slot]
    a, b = perm[2 * k], perm[2 * k + 1]
    tape = bytearray(prog(s0, a) + prog(s0, b))
    muts = []
    for i in range(128):
        rng = sm64(((n * es + k) * 128 + i) & M64)
        if ((rng >> 8) & ((1 << 30) - 1)) < (1 << 18):
            muts.append({"pos": i, "old": tape[i], "new": rng & 0xFF})
            tape[i] = rng & 0xFF
    pre = bytes(tape)
    run(tape)
    ok = bytes(tape[:64]) == prog(s1, a) and bytes(tape[64:]) == prog(s1, b)

    def status(p):
        r = arun(list(p) + [None] * 64)
        if r["ok"]:
            c = r["tape"][64:]
            if c == list(p[::-1]) and r["tape"][:64] == list(p): return "exact mirror copier for every partner (abstract run)"
            return "abstract run finishes, child not an exact copy"
        return f"not certifiable: {r['reason']} at step {r['step']}"
    records.append({
        "slot": slot, "pair_index": k, "left_slot": a, "right_slot": b,
        "parent_left": prog(s0, a).hex(), "parent_right": prog(s0, b).hex(),
        "mutations": muts, "tape_after_mutation": pre.hex(),
        "child_left": bytes(tape[:64]).hex(), "child_right": bytes(tape[64:]).hex(),
        "matches_saved_soup": ok,
        "which_child_is_lineage": "left" if slot == a else "right",
        "lineage_strand": lineage(prog(s1, slot)),
        "status": {"parent_left": status(prog(s0, a)), "parent_right": status(prog(s0, b)),
                   "child_left": status(bytes(tape[:64])), "child_right": status(bytes(tape[64:]))},
        "glyphs": {"parent_left": show(prog(s0, a)), "parent_right": show(prog(s0, b)),
                   "child_left": show(bytes(tape[:64])), "child_right": show(bytes(tape[64:])), "genome": show(G)},
    })
print(json.dumps({"seed": seed, "epoch_index": epoch, "lineage_before": len(before_hits), "lineage_after": len(born),
                  "births": records}, indent=1))
