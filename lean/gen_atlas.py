#!/usr/bin/env python3
"""Generate the ProofOfLife organism / birth-certificate modules.

Phase 1 writes gen/Checkpoints.lean, whose `#eval` runs the Lean abstract
interpreter (ProofOfLife.Abstract.aexecS) and prints the 16 checkpoint states
(every 512 steps) of each chain. Phase 2 writes one Lean module per chain group,
with the checkpoints as literals; every chunk `aexecS 512 cp_i = some cp_{i+1}`
is re-checked by the kernel (`decide +kernel`), so the checkpoints are untrusted.

Usage (from lean/):  python3 gen_atlas.py
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LAKE = os.path.expanduser("~/.elan/bin/lake")
CHUNK, NCH = 512, 16
OPS = set(b"<>{}+-.,[]")


def load(name):
    return json.load(open(os.path.join(ROOT, "data", name)))


def u8vec(b):
    rows = [", ".join("0x%02x" % x for x in b[i:i + 16]) for i in range(0, len(b), 16)]
    return "#v[\n  " + ",\n  ".join(rows) + "]"


def cellvec(tokens):
    out = []
    for t in tokens:
        out.append(".unk" if t == "u" else ".nz" if t == "z" else ".known %d" % int(t[1:]))
    rows = [", ".join(out[i:i + 16]) for i in range(0, len(out), 16)]
    return "#v[\n    " + ",\n    ".join(rows) + "]"


def modname(oid):  # world-30 -> World30, paper-fig4 -> PaperFig4
    return "".join(p[:1].upper() + p[1:] for p in oid.split("-"))


class Chain:
    """A chunked abstract run. `decls` must define what `start` mentions."""
    def __init__(self, cid, prefix, decls, start):
        self.cid, self.prefix, self.decls, self.start = cid, prefix, decls, start
        self.cps = None      # list of (pos, h0, h1, tokens) for cp1..cp16
        self.fail = None     # chunk index that failed

    def final_bytes(self):
        toks = self.cps[-1][3]
        if any(not t.startswith("k") for t in toks):
            return None
        return bytes(int(t[1:]) for t in toks)

    def final_tokens(self):
        return self.cps[-1][3]

    def lean(self):
        p = self.prefix
        L = [f"/-- Checkpoint 0 of chain `{p or 'main'}`. -/",
             f"def {p}cp0 : AState := {self.start}", ""]
        for i, (pos, h0, h1, toks) in enumerate(self.cps, 1):
            L.append(f"def {p}cp{i} : AState :=\n  ⟨{cellvec(toks)},\n   {pos}, {h0}, {h1}⟩\n")
        for i in range(NCH):
            L.append(f"theorem {p}chunk{i} : aexecS {CHUNK} {p}cp{i} = some {p}cp{i+1} := by decide +kernel")
        L.append("")
        L.append(f"theorem {p}run_ok : aexecS {CHUNK*NCH} {p}cp0 = some {p}cp{NCH} := by")
        L.append(f"  have h1 : aexecS {2*CHUNK} {p}cp0 = some {p}cp2 := aexecS_chain {p}chunk0 {p}chunk1 rfl")
        for i in range(2, NCH):
            L.append(f"  have h{i} : aexecS {(i+1)*CHUNK} {p}cp0 = some {p}cp{i+1} := "
                     f"aexecS_chain h{i-1} {p}chunk{i} rfl")
        L.append(f"  exact h{NCH-1}")
        L.append("")
        return "\n".join(L)


# ---------------------------------------------------------------- inputs
classify = {o["id"]: o for o in load("classify.json")}
abstract = {o["id"]: o for o in load("abstract.json")}
killers = {o["id"]: o for o in load("killers.json")}
birth = load("birth52_lean_inputs.json")

mirror_ids = [i for i, o in classify.items() if o["rule"] == "noheads"
              and abstract[i].get("abstract_ok") and abstract[i].get("child_is_mirror")]
copy_ids = [i for i, o in classify.items() if o["rule"] == "heads"
            and abstract[i].get("abstract_ok") and abstract[i].get("child_is_copy")]
killer_heads_ids = ["world-1006", "world-1007", "world-1008", "world-1011",
                    "world-1012", "world-1013", "world-1024"]
G = {i: bytes.fromhex(o["genome"]) for i, o in classify.items()}

only = sys.argv[1] if len(sys.argv) > 1 else "all"   # "birth" or "all"

# ---------------------------------------------------------------- chains
chains = {}
modules = []   # (relative module path, kind, builder)


def add_chain(c):
    chains[c.cid] = c
    return c


def pdecl(name, b):
    return f"def {name} : Vector UInt8 64 := {u8vec(b)}"


# Birth certificate (world 52)
bA, bB, bAo, bC, bkA, bkB = (bytes.fromhex(birth[k]) for k in
                             ["A", "B", "A_out", "C", "killer_A", "killer_B"])
bdecls = "\n".join([pdecl("A", bA), pdecl("B", bB), pdecl("A_out", bAo), pdecl("C", bC),
                    pdecl("killer_A", bkA), pdecl("killer_B", bkB), pdecl("Crev", bC[::-1])])
add_chain(Chain("birth/collision", "", bdecls, "startNH (liftT (A ++ B))"))
add_chain(Chain("birth/newborn", "", bdecls, "startNH (liftP C unk64)"))
add_chain(Chain("birth/newbornrev", "r", bdecls, "startNH (liftP Crev unk64)"))
add_chain(Chain("birth/parentA", "", bdecls, "startNH (liftT (A ++ killer_A))"))
add_chain(Chain("birth/parentB", "", bdecls, "startNH (liftT (B ++ killer_B))"))

if only == "all":
    for i in mirror_ids:
        P = G[i]
        add_chain(Chain(f"{i}/mirror", "", pdecl("P", P), "startNH (liftP P unk64)"))
        if P[::-1] != P:
            add_chain(Chain(f"{i}/rev", "r", pdecl("Q", P[::-1]), "startNH (liftP Q unk64)"))
    for i in copy_ids:
        add_chain(Chain(f"{i}/copy", "", pdecl("P", G[i]), "startH P (liftP P unk64)"))
    achB = "def achB : Vector ACell 64 := #v[" + ", ".join([".unk"] * 63 + [".nz"]) + "]"
    add_chain(Chain("world-50/achilles", "", pdecl("P", G["world-50"]) + "\n" + achB,
                    "startNH (liftP P achB)"))
    kb = bytes.fromhex(killers["world-50"]["killer"])
    add_chain(Chain("world-50/killer", "k", pdecl("P", G["world-50"]) + "\n" + pdecl("Bk", kb),
                    "startNH (liftT (P ++ Bk))"))
    for i in killer_heads_ids:
        kb = bytes.fromhex(killers[i]["killer"])
        add_chain(Chain(f"{i}/killer", "k", pdecl("P", G[i]) + "\n" + pdecl("Bk", kb),
                        "⟨liftT (P ++ Bk), 2, hd (P ++ Bk)[0], hd (P ++ Bk)[1]⟩"))

# ---------------------------------------------------------------- phase 1
os.makedirs(os.path.join(HERE, "gen"), exist_ok=True)
g = ["import ProofOfLife.Abstract", "open ProofOfLife", "",
     "def cellStr : ACell → String",
     "  | .known v => s!\"k{v.toNat}\"", "  | .unk => \"u\"", "  | .nz => \"z\"", "",
     "def dumpChain (name : String) (s0 : AState) : IO Unit := do",
     "  IO.println s!\"@@CHAIN {name}\"",
     "  let mut s := s0",
     f"  for i in [1:{NCH+1}] do",
     f"    match aexecS {CHUNK} s with",
     "    | some s' =>",
     "      IO.println s!\"@@CP {i} {s'.pos} {s'.h0.val} {s'.h1.val} {\",\".intercalate (s'.tape.toList.map cellStr)}\"",
     "      s := s'",
     "    | none =>",
     "      IO.println s!\"@@FAIL {i}\"",
     "      return", ""]
for n, c in enumerate(chains.values()):
    g += [f"namespace G{n}", "open ProofOfLife", c.decls, f"def start : AState := {c.start}",
          f"end G{n}", ""]
g.append("def main : IO Unit := do")
for n, c in enumerate(chains.values()):
    g.append(f"  dumpChain \"{c.cid}\" G{n}.start")
g += ["", "#eval main", ""]
open(os.path.join(HERE, "gen", "Checkpoints.lean"), "w").write("\n".join(g))
out = subprocess.run([LAKE, "env", "lean", "gen/Checkpoints.lean"], cwd=HERE,
                     capture_output=True, text=True)
if out.returncode != 0:
    print(out.stdout[-3000:], out.stderr[-3000:])
    sys.exit(1)
cur = None
for line in out.stdout.splitlines():
    if line.startswith("@@CHAIN "):
        cur = chains[line.split(" ", 1)[1]]
        cur.cps = []
    elif line.startswith("@@CP "):
        _, i, pos, h0, h1, cells = line.split(" ")
        cur.cps.append((int(pos), int(h0), int(h1), cells.split(",")))
    elif line.startswith("@@FAIL "):
        cur.fail = int(line.split()[1])
        cur.cps = None

status = {}
for c in chains.values():
    status[c.cid] = "FAIL at chunk %d" % c.fail if c.fail else "ok"
print(json.dumps(status, indent=1))


# ---------------------------------------------------------------- phase 2
HEADER = """import {imports}

/-! {doc}

Generated by `gen_atlas.py`. Checkpoints were printed by `#eval` and are NOT
trusted: every chunk is re-checked by the kernel (`decide +kernel`). -/

namespace {ns}
open ProofOfLife

"""


def write_module(path, imports, ns, doc, body):
    full = os.path.join(HERE, path)
    os.makedirs(os.path.dirname(full), exist_ok=True)
    text = HEADER.format(imports="\nimport ".join(imports), ns=ns, doc=doc) + body + f"\nend {ns}\n"
    open(full, "w").write(text)
    return path[:-5].replace("/", ".")


def pick_index(R, P, kind, prefer_child=True):
    """First index where tape R differs from P++P.reverse ('mirror') or P++P ('copy'),
    preferring child cells that should hold an opcode of P."""
    tgt = P + (P[::-1] if kind == "mirror" else P)
    diffs = [i for i in range(128) if R[i] != tgt[i]]
    if not diffs:
        return None
    def src(i):  # which P byte the child cell i should hold
        return (127 - i) if kind == "mirror" else (i - 64)
    code = [i for i in diffs if i >= 64 and P[src(i)] in OPS]
    child = [i for i in diffs if i >= 64]
    return (code or child or diffs)[0]


def hexs(b):
    return b.hex()


report = []   # entries for atlas_report.json (without timings)
built = []


def entry(oid, rule, kind, thm, stmt, mod, status, note=""):
    report.append(dict(id=oid, rule=rule, kind=kind, theorem=thm, statement=stmt,
                       module=mod, status=status, note=note))


# ---- birth certificate
BNS = "ProofOfLife.Birth52"
write_module("ProofOfLife/Birth52/Data.lean", ["ProofOfLife.Abstract"], BNS,
             "World 52 birth certificate: the genomes of the collision (from data/birth52_lean_inputs.json).",
             bdecls + "\n\ntheorem Crev_pointwise : ∀ i (hi : i < 64), Crev[i] = C[63 - i]'(by omega) := by\n"
             "  decide +kernel\n\ntheorem Crev_eq : Crev = C.reverse := rev_of_pointwise Crev_pointwise\n")
birth_ok = True
c = chains["birth/collision"]
if c.cps and c.final_bytes() == bAo + bC:
    body = c.lean() + (
        "theorem final_ok : ∀ i (hi : i < 128), cp16.tape[i] = ACell.known (A_out ++ C)[i] := by\n"
        "  decide +kernel\n\n"
        "/-- The collision itself: A meets B and leaves A_out ++ C. -/\n"
        "theorem collision : run (A ++ B) = A_out ++ C := exact_concrete run_ok final_ok\n")
    built.append(write_module("ProofOfLife/Birth52/Collision.lean", ["ProofOfLife.Birth52.Data"], BNS + ".Collision",
                              "World 52: the collision `run (A ++ B) = A_out ++ C`.", body))
else:
    birth_ok = False
    print("collision chain mismatch", c.fail)
c = chains["birth/newborn"]
if c.cps and c.final_bytes() == bC + bC[::-1]:
    body = c.lean() + (
        "theorem final_ok : IsMirrorOf C cp16.tape := by decide +kernel\n\n"
        "/-- The newborn is an exact mirror copier for every partner. -/\n"
        "theorem newborn_copies : ∀ X : Vector UInt8 64, run (C ++ X) = C ++ C.reverse :=\n"
        "  exact_mirror run_ok final_ok\n")
    built.append(write_module("ProofOfLife/Birth52/Newborn.lean", ["ProofOfLife.Birth52.Data"], BNS + ".Newborn",
                              "World 52: the newborn C copies itself mirror-reversed into any partner.", body))
else:
    birth_ok = False
    print("newborn chain mismatch", c.fail)
c = chains["birth/newbornrev"]
if c.cps and c.final_bytes() == bC[::-1] + bC:
    body = c.lean() + (
        "theorem rfinal_ok : IsMirrorOf Crev rcp16.tape := by decide +kernel\n\n"
        "theorem rev_mirror : ∀ X : Vector UInt8 64, run (Crev ++ X) = Crev ++ Crev.reverse :=\n"
        "  exact_mirror rrun_ok rfinal_ok\n\n"
        "/-- The newborn's mirror strand copies back into the newborn, for every partner. -/\n"
        "theorem newborn_lineage : ∀ X : Vector UInt8 64, run (C.reverse ++ X) = C.reverse ++ C := by\n"
        "  intro X\n  have h := rev_mirror X\n  rw [Crev_eq, Vector.reverse_reverse] at h\n  exact h\n")
    built.append(write_module("ProofOfLife/Birth52/NewbornRev.lean", ["ProofOfLife.Birth52.Data"], BNS + ".NewbornRev",
                              "World 52: the newborn's mirror strand C.reverse copies back into C.", body))
else:
    birth_ok = False
    print("newbornrev chain mismatch", c.fail)
for par, Pb, kb, nm in [("A", bA, bkA, "parentA"), ("B", bB, bkB, "parentB")]:
    c = chains[f"birth/{nm}"]
    R = c.final_bytes() if c.cps else None
    if R is None:
        birth_ok = False
        print(nm, "chain failed")
        continue
    im, ic = pick_index(R, Pb, "mirror"), pick_index(R, Pb, "copy")
    if im is None or ic is None:
        birth_ok = False
        print(nm, "killer does not kill", im, ic)
        continue
    rn = f"R{par}"
    body = c.lean() + (
        f"/-- Final tape of `{par} ++ killer_{par}`. -/\n"
        f"def {rn} : Tape := ⟨#[{', '.join('0x%02x' % x for x in R)}], rfl⟩\n\n"
        f"theorem final_ok : ∀ i (hi : i < 128), cp16.tape[i] = ACell.known {rn}[i] := by\n"
        f"  decide +kernel\n\n"
        f"theorem parent_{par}_run : run ({par} ++ killer_{par}) = {rn} := exact_concrete run_ok final_ok\n\n"
        f"/-- Parent {par} is not a replicator: against `killer_{par}` it produces neither its\n"
        f"mirror nor its forward copy (differs at bytes {im} and {ic}). -/\n"
        f"theorem parent_{par}_not_replicator :\n"
        f"    run ({par} ++ killer_{par}) ≠ {par} ++ {par}.reverse ∧ run ({par} ++ killer_{par}) ≠ {par} ++ {par} :=\n"
        f"  ⟨ne_mirror {im} (by decide) (by rw [parent_{par}_run]; decide +kernel),\n"
        f"   ne_copy {ic} (by decide) (by rw [parent_{par}_run]; decide +kernel)⟩\n")
    built.append(write_module(f"ProofOfLife/Birth52/Parent{par}.lean", ["ProofOfLife.Birth52.Data"], BNS + f".Parent{par}",
                              f"World 52: parent {par} is not a replicator (explicit killer partner).", body))
BIRTH_STMT = ("run (A ++ B) = A_out ++ C ∧ (∀ X : Vector UInt8 64, run (C ++ X) = C ++ C.reverse) ∧ "
              "(∀ X : Vector UInt8 64, run (C.reverse ++ X) = C.reverse ++ C) ∧ "
              "(run (A ++ killer_A) ≠ A ++ A.reverse ∧ run (A ++ killer_A) ≠ A ++ A) ∧ "
              "(run (B ++ killer_B) ≠ B ++ B.reverse ∧ run (B ++ killer_B) ≠ B ++ B)")
if birth_ok:
    body = ("/-- **Birth certificate of life in world 52.** The recorded collision produced C;\n"
            "C and its mirror strand copy each other for every partner; neither parent is a\n"
            "replicator. -/\n"
            "theorem birth_certificate_world52 :\n"
            "    run (A ++ B) = A_out ++ C ∧\n"
            "    (∀ X : Vector UInt8 64, run (C ++ X) = C ++ C.reverse) ∧\n"
            "    (∀ X : Vector UInt8 64, run (C.reverse ++ X) = C.reverse ++ C) ∧\n"
            "    (run (A ++ killer_A) ≠ A ++ A.reverse ∧ run (A ++ killer_A) ≠ A ++ A) ∧\n"
            "    (run (B ++ killer_B) ≠ B ++ B.reverse ∧ run (B ++ killer_B) ≠ B ++ B) :=\n"
            "  ⟨Collision.collision, Newborn.newborn_copies, NewbornRev.newborn_lineage,\n"
            "   ParentA.parent_A_not_replicator, ParentB.parent_B_not_replicator⟩\n")
    built.append(write_module("ProofOfLife/Birth52/Certificate.lean",
                              ["ProofOfLife.Birth52.Collision", "ProofOfLife.Birth52.Newborn",
                               "ProofOfLife.Birth52.NewbornRev", "ProofOfLife.Birth52.ParentA",
                               "ProofOfLife.Birth52.ParentB"], BNS,
                              "World 52 birth certificate (bundle).", body))
    entry("world-52-birth", "noheads", "birth", "ProofOfLife.Birth52.birth_certificate_world52",
          BIRTH_STMT, "ProofOfLife.Birth52.Certificate", "generated")
else:
    entry("world-52-birth", "noheads", "birth", "ProofOfLife.Birth52.birth_certificate_world52",
          BIRTH_STMT, "", "failed", "abstract/concrete chain did not produce the expected result")

# ---- atlas
if only == "all":
    for i in mirror_ids:
        P, N = G[i], modname(i)
        ns = f"ProofOfLife.{N}"
        c = chains[f"{i}/mirror"]
        stmt = "∀ B : Vector UInt8 64, run (P ++ B) = P ++ P.reverse"
        if c.cps and c.final_bytes() == P + P[::-1]:
            body = pdecl("P", P) + "\n\n" + c.lean() + (
                "theorem final_ok : IsMirrorOf P cp16.tape := by decide +kernel\n\n"
                f"/-- **{i}** copies itself mirror-reversed into every partner. -/\n"
                f"theorem mirror : {stmt} :=\n  exact_mirror run_ok final_ok\n")
            m = write_module(f"ProofOfLife/Organisms/{N}.lean", ["ProofOfLife.Abstract"], ns,
                             f"{i} (noheads): exact mirror copy for every partner. Genome {hexs(P)}", body)
            built.append(m)
            entry(i, "noheads", "exact", f"{ns}.mirror", stmt, m, "generated")
        else:
            entry(i, "noheads", "exact", f"{ns}.mirror", stmt, "", "failed",
                  f"abstract run: fail at chunk {c.fail}" if c.fail else "final tape is not the mirror")
            continue
        lstmt = "∀ B : Vector UInt8 64, run (P.reverse ++ B) = P.reverse ++ P"
        if P[::-1] == P:
            body = ("theorem pal_pointwise : ∀ i (hi : i < 64), P[i] = P[63 - i]'(by omega) := by\n"
                    "  decide +kernel\n\n"
                    "theorem palindrome : P.reverse = P := (rev_of_pointwise pal_pointwise).symm\n\n"
                    f"/-- {i} is a palindrome, so its mirror strand is itself. -/\n"
                    f"theorem lineage : {lstmt} := by\n"
                    "  intro B; rw [palindrome]; have h := mirror B; rw [palindrome] at h; exact h\n\n"
                    "theorem lineage_closed : (∀ B : Vector UInt8 64, run (P ++ B) = P ++ P.reverse) ∧\n"
                    "    (∀ B : Vector UInt8 64, run (P.reverse ++ B) = P.reverse ++ P) :=\n"
                    "  ⟨mirror, lineage⟩\n")
            m = write_module(f"ProofOfLife/Organisms/{N}Lineage.lean", [f"ProofOfLife.Organisms.{N}"], ns,
                             f"{i}: lineage (palindrome).", body)
            built.append(m)
            entry(i, "noheads", "lineage", f"{ns}.lineage_closed",
                  "(∀ B, run (P ++ B) = P ++ P.reverse) ∧ (∀ B, run (P.reverse ++ B) = P.reverse ++ P)",
                  m, "generated", "palindrome")
            continue
        c = chains[f"{i}/rev"]
        if c.cps and c.final_bytes() == P[::-1] + P:
            body = pdecl("Q", P[::-1]) + "\n\n" + (
                "theorem Q_pointwise : ∀ i (hi : i < 64), Q[i] = P[63 - i]'(by omega) := by\n"
                "  decide +kernel\n\n"
                "theorem Q_eq : Q = P.reverse := rev_of_pointwise Q_pointwise\n\n") + c.lean() + (
                "theorem rfinal_ok : IsMirrorOf Q rcp16.tape := by decide +kernel\n\n"
                "theorem rev_mirror : ∀ B : Vector UInt8 64, run (Q ++ B) = Q ++ Q.reverse :=\n"
                "  exact_mirror rrun_ok rfinal_ok\n\n"
                f"/-- The mirror strand of {i} copies back into {i}, for every partner. -/\n"
                f"theorem lineage : {lstmt} := by\n"
                "  intro B\n  have h := rev_mirror B\n  rw [Q_eq, Vector.reverse_reverse] at h\n  exact h\n\n"
                "/-- Both strands copy each other for any partner. -/\n"
                "theorem lineage_closed : (∀ B : Vector UInt8 64, run (P ++ B) = P ++ P.reverse) ∧\n"
                "    (∀ B : Vector UInt8 64, run (P.reverse ++ B) = P.reverse ++ P) :=\n"
                "  ⟨mirror, lineage⟩\n")
            m = write_module(f"ProofOfLife/Organisms/{N}Lineage.lean", [f"ProofOfLife.Organisms.{N}"], ns,
                             f"{i}: lineage — the mirror strand copies back.", body)
            built.append(m)
            entry(i, "noheads", "lineage", f"{ns}.lineage_closed",
                  "(∀ B, run (P ++ B) = P ++ P.reverse) ∧ (∀ B, run (P.reverse ++ B) = P.reverse ++ P)",
                  m, "generated")
        else:
            why = f"abstract run of P.reverse ++ ? gives up at chunk {c.fail}" if c.fail else \
                "abstract run of P.reverse ++ ? does not end in P.reverse ++ P"
            entry(i, "noheads", "lineage", f"{ns}.lineage_closed", lstmt, "", "failed", why)
    for i in copy_ids:
        P, N = G[i], modname(i)
        ns = f"ProofOfLife.{N}"
        c = chains[f"{i}/copy"]
        stmt = "∀ B : Vector UInt8 64, runHeads (P ++ B) = P ++ P"
        if c.cps and c.final_bytes() == P + P:
            body = pdecl("P", P) + "\n\n" + c.lean() + (
                "theorem final_ok : IsCopyOf P cp16.tape := by decide +kernel\n\n"
                f"/-- **{i}** (heads rule) copies itself forward into every partner. -/\n"
                f"theorem copy : {stmt} :=\n  exact_copy_heads run_ok final_ok\n")
            m = write_module(f"ProofOfLife/Organisms/{N}.lean", ["ProofOfLife.Abstract"], ns,
                             f"{i} (heads): exact forward copy for every partner. Genome {hexs(P)}", body)
            built.append(m)
            entry(i, "heads", "exact", f"{ns}.copy", stmt, m, "generated")
        else:
            entry(i, "heads", "exact", f"{ns}.copy", stmt, "", "failed",
                  f"abstract run: fail at chunk {c.fail}" if c.fail else "final tape is not the copy")
    # Achilles (world-50)
    P, ns = G["world-50"], "ProofOfLife.World50"
    c = chains["world-50/achilles"]
    astmt = "∀ B : Vector UInt8 64, B[63] ≠ 0 → run (P ++ B) = P ++ P.reverse"
    if c.cps and c.final_bytes() == P + P[::-1]:
        achB = "def achB : Vector ACell 64 := #v[" + ", ".join([".unk"] * 63 + [".nz"]) + "]"
        body = pdecl("P", P) + "\n\n/-- Partner: unknown bytes, except the last one is nonzero. -/\n" + achB + "\n\n" + \
            c.lean() + (
                "theorem final_ok : IsMirrorOf P cp16.tape := by decide +kernel\n\n"
                "theorem achB_shape : ∀ j (h : j < 64), achB[j] = if j = 63 then ACell.nz else ACell.unk := by\n"
                "  decide +kernel\n\n"
                "theorem partnerOK_achB (B : Vector UInt8 64) (hB : B[63] ≠ 0) : PartnerOK B achB := by\n"
                "  intro j h\n  rw [achB_shape j h]\n  by_cases hj : j = 63\n"
                "  · subst hj; simp only [if_true, CellAgrees]; exact hB\n"
                "  · simp only [hj, if_false, CellAgrees]\n\n"
                "/-- **Achilles.** world-50 mirror-copies itself into every partner whose last byte\n"
                "(tape cell 127, tested by its loop before it is overwritten) is nonzero. -/\n"
                f"theorem achilles : {astmt} :=\n"
                "  fun B hB => guarded_mirror run_ok final_ok B (partnerOK_achB B hB)\n")
        m = write_module("ProofOfLife/Organisms/World50Achilles.lean", ["ProofOfLife.Abstract"], ns,
                         f"world-50 (noheads): Achilles heel. Genome {hexs(P)}", body)
        built.append(m)
        entry("world-50", "noheads", "achilles", f"{ns}.achilles", astmt, m, "generated")
    else:
        entry("world-50", "noheads", "achilles", f"{ns}.achilles", astmt, "", "failed",
              f"abstract run: fail at chunk {c.fail}" if c.fail else "final tape is not the mirror")
    # Killers
    kjobs = [("world-50", "noheads", "mirror")] + [(i, "heads", "copy") for i in killer_heads_ids]
    for i, rule, kind in kjobs:
        P, N = G[i], modname(i)
        ns = f"ProofOfLife.{N}"
        c = chains[f"{i}/killer"]
        kb = bytes.fromhex(killers[i]["killer"])
        R = c.final_bytes() if c.cps else None
        runf = "run" if rule == "noheads" else "runHeads"
        tgt = "P ++ P.reverse" if kind == "mirror" else "P ++ P"
        stmt = f"{runf} (P ++ Bk) ≠ {tgt}"
        idx = pick_index(R, P, kind) if R else None
        if R is None or idx is None:
            entry(i, rule, "killer", f"{ns}.killer", stmt, "", "failed",
                  "run failed" if R is None else "killer partner does not change the expected result")
            continue
        j = (127 - idx) if kind == "mirror" else (idx - 64)
        exact_thm = "exact_concrete" if rule == "noheads" else "exact_concrete_heads"
        ne_thm = "ne_mirror" if kind == "mirror" else "ne_copy"
        is_code = idx >= 64 and P[j] in OPS
        code_txt = ""
        if idx >= 64:
            code_txt = (f"/-- The child's byte {idx} should be `P[{j}]`"
                        f"{' (an opcode)' if is_code else ''} but is not. -/\n"
                        f"theorem killer_code : ({runf} (P ++ Bk))[{idx}] ≠ P[{j}] := by\n"
                        f"  rw [killer_run]; decide +kernel\n\n")
        body = pdecl("P", P) + "\n\n/-- Killer partner (data/killers.json). -/\n" + pdecl("Bk", kb) + "\n\n" + \
            c.lean() + (
                f"/-- Final tape of `P ++ Bk`. -/\n"
                f"def R : Tape := ⟨#[{', '.join('0x%02x' % x for x in R)}], rfl⟩\n\n"
                f"theorem kfinal_ok : ∀ i (hi : i < 128), kcp16.tape[i] = ACell.known R[i] := by\n"
                f"  decide +kernel\n\n"
                f"theorem killer_run : {runf} (P ++ Bk) = R := {exact_thm} krun_ok kfinal_ok\n\n"
                + code_txt +
                f"/-- **Killer.** Against partner `Bk`, {i} does not produce {tgt}. -/\n"
                f"theorem killer : {stmt} :=\n"
                f"  {ne_thm} {idx} (by decide) (by rw [killer_run]; decide +kernel)\n")
        imports = ["ProofOfLife.Abstract"]
        ach_ok = any(e["kind"] == "achilles" and e["status"] == "generated" for e in report)
        if i == "world-50" and ach_ok:
            # same namespace as the Achilles module: reuse its `P`
            body = body.replace(pdecl("P", P) + "\n\n", "", 1)
            imports = ["ProofOfLife.Organisms.World50Achilles"]
        m = write_module(f"ProofOfLife/Organisms/{N}Killer.lean", imports, ns,
                         f"{i} ({rule}): an explicit killer partner. Survival {killers[i]['survival']}.", body)
        built.append(m)
        entry(i, rule, "killer", f"{ns}.killer", stmt, m, "generated",
              f"differs at byte {idx}" + (f"; killer_code: child byte {idx} != P[{j}]" +
                                           (" (opcode)" if is_code else "") if idx >= 64 else ""))

json.dump(dict(modules=built, entries=report, chain_status=status),
          open(os.path.join(HERE, "gen", "manifest.json"), "w"), indent=1)
print(len(built), "modules written")
