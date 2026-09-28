#!/usr/bin/env python3
"""Abstract BFF interpreter: the partner's bytes are unknown (None).

Mirrors the abstract semantics used in lean/MirrorLife.lean: the run gives up
("depends on the partner") whenever the concrete behaviour could depend on an
unknown byte — fetching an unknown opcode, testing an unknown byte at [ or ],
or a bracket scan passing over an unknown byte. Arithmetic and copies simply
propagate unknowns. If the run finishes, every known byte of the final tape is
the same for all 256^64 partners.

For each organism we report which bytes of the child are guaranteed, and for
runs that give up, the step, position and reason — the organism's weak spot.
"""
import json, os, sys

UNKNOWN = None


def arun(tape, heads=False, steps=8192):
    t = list(tape)
    pos = h0 = h1 = 0
    if heads:
        if t[0] is None or t[1] is None:
            return {"ok": False, "step": 0, "reason": "initial head read from an unknown byte", "at": 0}
        h0, h1, pos = t[0] % 128, t[1] % 128, 2
    for i in range(steps):
        h0 &= 127
        h1 &= 127
        c = t[pos]
        if c is UNKNOWN:
            return {"ok": False, "step": i, "reason": "would execute a partner byte", "at": pos}
        if c == 60: h0 -= 1
        elif c == 62: h0 += 1
        elif c == 123: h1 -= 1
        elif c == 125: h1 += 1
        elif c == 43: t[h0] = None if t[h0] is None else (t[h0] + 1) & 255
        elif c == 45: t[h0] = None if t[h0] is None else (t[h0] - 1) & 255
        elif c == 46: t[h1] = t[h0]
        elif c == 44: t[h0] = t[h1]
        elif c == 91:
            if t[h0] is None:
                return {"ok": False, "step": i, "reason": "loop test reads a partner byte", "at": h0}
            if t[h0] == 0:
                d = 1; pos += 1
                while pos < 128 and d > 0:
                    if t[pos] is None:
                        return {"ok": False, "step": i, "reason": "bracket scan crosses a partner byte", "at": pos}
                    if t[pos] == 93: d -= 1
                    if t[pos] == 91: d += 1
                    pos += 1
                pos -= 1
                if d != 0: pos = 128
        elif c == 93:
            if t[h0] is None:
                return {"ok": False, "step": i, "reason": "loop test reads a partner byte", "at": h0}
            if t[h0] != 0:
                d = 1; pos -= 1
                while pos >= 0 and d > 0:
                    if t[pos] is None:
                        return {"ok": False, "step": i, "reason": "bracket scan crosses a partner byte", "at": pos}
                    if t[pos] == 93: d += 1
                    if t[pos] == 91: d -= 1
                    pos -= 1
                pos += 1
                if d != 0:
                    return {"ok": True, "tape": t, "steps": i + 1}
        pos += 1
        if pos >= 128:
            return {"ok": True, "tape": t, "steps": i + 1}
    return {"ok": True, "tape": t, "steps": steps}


if __name__ == "__main__":
    ROOT = os.path.join(os.path.dirname(__file__), "..")
    orgs = json.load(open(os.path.join(ROOT, "data/classify.json")))
    out = []
    for o in orgs:
        P = list(bytes.fromhex(o["genome"]))
        heads = o["rule"] == "heads"
        r = arun(P + [UNKNOWN] * 64, heads=heads)
        rec = {"id": o["id"], "rule": o["rule"], "class": o["class"], "abstract_ok": r["ok"]}
        if r["ok"]:
            child = r["tape"][64:]
            parent = r["tape"][:64]
            rev = P[::-1]
            known = [i for i in range(64) if child[i] is not None]
            rec["parent_intact"] = parent == P
            rec["child_known"] = len(known)
            rec["child_is_mirror"] = child == rev
            rec["child_is_copy"] = child == P
            # which child bytes are guaranteed to equal the genome (forward) or its mirror
            rec["fwd_guaranteed"] = sum(child[i] == P[i] for i in range(64))
            rec["rev_guaranteed"] = sum(child[i] == rev[i] for i in range(64))
            code = [i for i in range(64) if P[i] in b"<>{}+-.,[]"]
            rec["code_guaranteed_fwd"] = all(child[i] == P[i] for i in code)
            rec["code_positions"] = len(code)
            rec["child_mask"] = "".join("K" if c is not None else "?" for c in child)
        else:
            rec.update({k: r[k] for k in ("step", "reason", "at")})
        out.append(rec)
    json.dump(out, open(os.path.join(ROOT, "data/abstract.json"), "w"), indent=1)
    from collections import Counter
    print(Counter((x["rule"], x["abstract_ok"], x.get("child_is_mirror") or x.get("child_is_copy") or ("code" if x.get("code_guaranteed_fwd") else "")) for x in out))
    for x in out:
        if not x["abstract_ok"]:
            print(x["id"], x["rule"], "GIVES UP at step", x["step"], "-", x["reason"], "@", x["at"])
        elif not (x.get("child_is_mirror") or x.get("child_is_copy")):
            print(x["id"], x["rule"], "partial: child known", x["child_known"], "fwd-guaranteed", x["fwd_guaranteed"], "code kept", x["code_guaranteed_fwd"], x["code_positions"], x["child_mask"])
