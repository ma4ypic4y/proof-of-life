"""Independent Python BFF interpreter (cubff semantics) with copy tracing.

Used to analyse replicators found by the C engine. Deliberately written from
the cubff source rather than from tol.c, so it doubles as a second check.
"""
import random

OPS = set(b"<>{}+-.,[]")


def run(tape, steps=8192, heads=False, trace=None):
    """Run a 128-byte tape in place. trace(kind, src, dst) is called for copies."""
    t = tape
    pos = h0 = h1 = 0
    if heads:
        h0, h1, pos = t[0] % 128, t[1] % 128, 2
    for _ in range(steps):
        h0 &= 127
        h1 &= 127
        c = t[pos]
        if c == 60: h0 -= 1          # <
        elif c == 62: h0 += 1        # >
        elif c == 123: h1 -= 1       # {
        elif c == 125: h1 += 1       # }
        elif c == 43: t[h0] = (t[h0] + 1) & 255
        elif c == 45: t[h0] = (t[h0] - 1) & 255
        elif c == 46:                # .  tape[h1] = tape[h0]
            if trace: trace(".", h0, h1)
            t[h1] = t[h0]
        elif c == 44:                # ,  tape[h0] = tape[h1]
            if trace: trace(",", h1, h0)
            t[h0] = t[h1]
        elif c == 91 and t[h0] == 0:  # [
            d = 1
            pos += 1
            while pos < 128 and d > 0:
                if t[pos] == 93: d -= 1
                if t[pos] == 91: d += 1
                pos += 1
            pos -= 1
            if d != 0:
                pos = 128
        elif c == 93 and t[h0] != 0:  # ]
            d = 1
            pos -= 1
            while pos >= 0 and d > 0:
                if t[pos] == 93: d += 1
                if t[pos] == 91: d -= 1
                pos -= 1
            pos += 1
            if d != 0:
                return
        pos += 1
        if pos >= 128:
            return


def show(b):
    return "".join(chr(c) if c in OPS else ("0" if c == 0 else "·") for c in b)


def copy_geometry(prog, trials=16, seed=0, heads=False):
    """Place prog on the left, random partners on the right; classify copies of
    the program's own bytes into the partner half as mirror (dst = 127 - src)
    or translation (dst = src + 64). Returns counts over all trials."""
    rng = random.Random(seed)
    res = {"mirror": 0, "shift": 0, "other": 0, "rev": 0, "fwd": 0}
    for _ in range(trials):
        tape = bytearray(prog) + bytearray(rng.randrange(256) for _ in range(64))
        last = [None]
        def tr(kind, src, dst):
            if src < 64 <= dst:
                if dst == 127 - src: res["mirror"] += 1
                elif dst == src + 64: res["shift"] += 1
                else: res["other"] += 1
                # direction between consecutive copies by the same instruction:
                # did the read and write heads step the same way (forward copy)
                # or opposite ways (reversed)? Wrap-aware, small steps only.
                if last[0] is not None and last[0][2] == kind:
                    ds = (src - last[0][0] + 192) % 128 - 64
                    dd = (dst - last[0][1] + 192) % 128 - 64
                    if ds and dd and abs(ds) <= 8 and abs(dd) <= 8:
                        res["rev" if (ds > 0) != (dd > 0) else "fwd"] += 1
                last[0] = (src, dst, kind)
        run(tape, heads=heads, trace=tr)
    return res


def mirror_skeleton(prog):
    """Fraction of instruction bytes whose mirror position holds the same instruction."""
    idx = [i for i in range(64) if prog[i] in OPS]
    if not idx:
        return 0.0
    return sum(prog[63 - i] == prog[i] for i in idx) / len(idx)


def offspring_identity(prog, trials=16, seed=1, heads=False):
    """After one interaction with a random partner, how much of the partner half
    equals prog, and how much equals reversed prog (byte identity, 0..1)."""
    rng = random.Random(seed)
    fwd = rev = 0.0
    r = bytes(reversed(prog))
    for _ in range(trials):
        tape = bytearray(prog) + bytearray(rng.randrange(256) for _ in range(64))
        run(tape, heads=heads)
        child = tape[64:]
        fwd += sum(a == b for a, b in zip(child, prog)) / 64
        rev += sum(a == b for a, b in zip(child, r)) / 64
    return fwd / trials, rev / trials


def copy_positions(prog, trials=8, seed=3, heads=False):
    """Positions (in prog's own coordinates, 0..63) of the copy instructions that
    move prog's bytes into its partner, when prog sits on the left of a random partner."""
    rng = random.Random(seed)
    pcs = set()
    for _ in range(trials):
        t = bytearray(prog) + bytearray(rng.randrange(256) for _ in range(64))
        pos = h0 = h1 = 0
        if heads:
            h0, h1, pos = t[0] % 128, t[1] % 128, 2
        for _ in range(8192):
            h0 &= 127
            h1 &= 127
            c = t[pos]
            if c == 60: h0 -= 1
            elif c == 62: h0 += 1
            elif c == 123: h1 -= 1
            elif c == 125: h1 += 1
            elif c == 43: t[h0] = (t[h0] + 1) & 255
            elif c == 45: t[h0] = (t[h0] - 1) & 255
            elif c == 46:
                if h0 < 64 <= h1 and pos < 64: pcs.add(pos)
                t[h1] = t[h0]
            elif c == 44:
                if h1 < 64 <= h0 and pos < 64: pcs.add(pos)
                t[h0] = t[h1]
            elif c == 91 and t[h0] == 0:
                d = 1
                pos += 1
                while pos < 128 and d > 0:
                    if t[pos] == 93: d -= 1
                    if t[pos] == 91: d += 1
                    pos += 1
                pos -= 1
                if d != 0: pos = 128
            elif c == 93 and t[h0] != 0:
                d = 1
                pos -= 1
                while pos >= 0 and d > 0:
                    if t[pos] == 93: d += 1
                    if t[pos] == 91: d -= 1
                    pos -= 1
                pos += 1
                if d != 0: break
            pos += 1
            if pos >= 128: break
    return sorted(pcs)
