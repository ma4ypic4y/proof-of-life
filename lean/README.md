# Proof of Life: a formally verified atlas of evolved BFF organisms

Lean 4.21.0, core only (no Mathlib, Std or Batteries). Every theorem below is checked by
Lean's kernel. The computations use `decide +kernel`. There is **no `native_decide`, no
`sorry`, no `admit`, and no new axiom**.

## Results

| Kind | Proved | Organisms | Theorem shape |
|---|---|---|---|
| **birth** | 1 / 1 | world-52 collision | `birth_certificate_world52` (below) |
| **exact**, paper rule | 22 / 22 | paper-fig4, world-2, world-7, world-10, world-11, world-12, world-15, world-29, world-30, world-32, world-33, world-37, world-38, world-41, world-42, world-46, world-48, world-49, world-52, world-55, world-56, world-58 | `∀ B, run (P ++ B) = P ++ P.reverse` |
| **exact**, heads rule | 7 / 7 | world-1005, world-1009, world-1014, world-1016, world-1021, world-1027, world-1028 | `∀ B, runHeads (P ++ B) = P ++ P` |
| **lineage** | 21 / 22 | all paper-rule mirror copiers except world-55 (paper-fig4 and world-29 are palindromes) | `lineage_closed` |
| **achilles** | 1 / 1 | world-50 | `∀ B, B[63] ≠ 0 → run (P ++ B) = P ++ P.reverse` |
| **killer** | 8 / 8 | world-50, world-1006, world-1007, world-1008, world-1011, world-1012, world-1013, world-1024 | `run(Heads) (P ++ Bk) ≠ …`, plus the opcode byte the child gets wrong |

**Not proved:**
- **world-55 lineage.** The abstract run of `P.reverse ++ [unknown × 64]` gives up at step 32:
  the reverse strand's loop tests partner byte 62 (tape cell 126) before overwriting it.
  Splitting that byte into "nonzero" and "0" cases also gives up later. Empirically the
  reverse strand copies exactly for 500/500 random partners. world-55's forward theorem
  (`ProofOfLife.World55.mirror`) **is** proved.
- **Skipped killers.** world-1004, world-1022 and world-1403 have no known killer partner
  (survival 1.0 in `data/killers.json`).

**Axioms.** `Atlas.lean` runs `#print axioms` on all 60 main theorems. Every one depends
only on **`[propext, Quot.sound]`**, Lean's standard axioms. There is no `Lean.ofReduceBool`
(so no `native_decide`) and no `sorryAx`. See `logs/atlas_axioms.txt`.

**Check time.**
- The sum of per-module build wall-clock is 10261 s. That was
  measured under heavy parallel load on a MacBook and a Mac mini, so it is an upper bound.
- On an unloaded Mac mini with 4–5 parallel jobs, a 16-chunk module takes about 130–170 s
  for an exact theorem, 40–70 s for a lineage module, and 18–28 s for a killer (killer runs
  halt early).
- The birth certificate took 547 s over 6 modules on the MacBook,
  with 5 in parallel. The collision module alone took 197 s.
- Per-module times, and which machine checked each module, are in `atlas_report.json`.

**How it was built.** The Mac mini ran out of memory, dropped off the network and
rebooted in the middle of the run, so the modules were checked on two machines with the
same sources and Lean 4.21.0:
- Each module was checked by its own `lake build <module>` (exit 0). The logs are in
  `logs/` and `logs/mac_mini/`.
- `lake env lean Atlas.lean` then elaborated the atlas against all the resulting `.olean`
  files.
- Many modules were also checked independently on both machines
  (`also_checked_on_mac_mini` in the report).

**End-to-end check.** After the distributed run, a single whole-project `lake build` on
the Mac mini finished with **"Build completed successfully"** (exit 0, 74 jobs, 263 s wall).
It built the 8 modules that machine still lacked and found every other module up to date
from its own earlier builds. There, too, `#print axioms` gives `[propext, Quot.sound]` for
all 60 theorems. See `logs/mac_mini/fullbuild.log` and `logs/mac_mini/atlas_axioms.txt`.

### Example statements (one per kind)

```lean
-- birth (ProofOfLife.Birth52.birth_certificate_world52)
theorem birth_certificate_world52 :
    run (A ++ B) = A_out ++ C ∧
    (∀ X : Vector UInt8 64, run (C ++ X) = C ++ C.reverse) ∧
    (∀ X : Vector UInt8 64, run (C.reverse ++ X) = C.reverse ++ C) ∧
    (run (A ++ killer_A) ≠ A ++ A.reverse ∧ run (A ++ killer_A) ≠ A ++ A) ∧
    (run (B ++ killer_B) ≠ B ++ B.reverse ∧ run (B ++ killer_B) ≠ B ++ B)

-- exact, paper rule (ProofOfLife.World30.mirror)
theorem mirror : ∀ B : Vector UInt8 64, run (P ++ B) = P ++ P.reverse

-- exact, heads rule (ProofOfLife.World1005.copy)
theorem copy : ∀ B : Vector UInt8 64, runHeads (P ++ B) = P ++ P

-- lineage (ProofOfLife.World30.lineage_closed)
theorem lineage_closed : (∀ B : Vector UInt8 64, run (P ++ B) = P ++ P.reverse) ∧
    (∀ B : Vector UInt8 64, run (P.reverse ++ B) = P.reverse ++ P)

-- achilles (ProofOfLife.World50.achilles)
theorem achilles : ∀ B : Vector UInt8 64, B[63] ≠ 0 → run (P ++ B) = P ++ P.reverse

-- killer (ProofOfLife.World1013.killer, killer_code)
theorem killer : runHeads (P ++ Bk) ≠ P ++ P
theorem killer_code : (runHeads (P ++ Bk))[68] ≠ P[4]     -- P[4] is an opcode
```

In each module `P` is the organism's genome, written out as a byte literal, and `Bk` is the
killer partner from `data/killers.json`. For world 52, `A`, `B`, `A_out`, `C`, `killer_A`
and `killer_B` come from `data/birth52_lean_inputs.json`. The certificate's concrete parts
also fix the exact final tapes: `run (A ++ killer_A) = RA` and `run (B ++ killer_B) = RB`.


## Layout

| Path | Contents |
|---|---|
| `ProofOfLife/Semantics.lean` | **The specification.** The concrete interpreter, one step function for both rules. `run`: noheads, the paper's rule (pos = h0 = h1 = 0). `runHeads`: cubff's `bff` rule (h0 = t[0] % 128, h1 = t[1] % 128, pos = 2). At most 8192 iterations. This is the only file a reader has to check against `analysis/bff.py` and `engine/tol.c`. |
| `ProofOfLife/Abstract.lean` | The abstract interpreter over cells `known v`, `unk` and `nz` (unknown but nonzero), plus the soundness proof (`aexecS_sound`, once for both rules), chunk composition (`aexecS_chain`) and the generic theorems each module uses: `exact_mirror`, `exact_copy_heads`, `guarded_mirror`, `exact_concrete(_heads)`, `ne_mirror`, `ne_copy`. |
| `ProofOfLife/Organisms/*.lean` | One generated module per organism and kind. |
| `ProofOfLife/Birth52/*.lean` | The world-52 birth certificate. |
| `Atlas.lean` | Imports everything and runs `#print axioms` on every main theorem. |
| `atlas_report.json` | Machine-readable report: per organism, id, rule, kind, theorem, statement, module, check seconds, axioms and status, plus totals. |
| `gen_atlas.py` | Generator. It prints the checkpoints with `#eval` and writes the modules. |
| `make_report.py` | Assembles `atlas_report.json` from the build logs. |
| `build_timed.sh`, `build_one.sh` | Parallel build with per-module timing. |
| `logs/` | Per-module build logs and times (`times_*.txt`), `atlas_axioms.txt`, and `mac_mini/` (that machine's module logs, `fullbuild.log`, `atlas_axioms.txt`). |
| `CheckPOL.lean`, `test_vectors*.txt`, `gen_vectors.py` | Cross-check of `run` and `runHeads` against `bff.py`. |
| `MirrorLife.lean`, `Check.lean` | The original single-organism proof for world 30. It is superseded by `ProofOfLife.World30`, but still builds. |

## How a proof works

1. **Abstract domain.** A tape cell is `known v`, `unk` (any byte) or `nz` (any nonzero
   byte). The abstract run **gives up** whenever the concrete behaviour could depend on a
   non-`known` cell. That covers four cases:
   - fetching it as an opcode;
   - crossing it during a bracket scan;
   - testing an `unk` cell at `[` or `]` (an `nz` cell counts as nonzero);
   - applying `+` or `-` to a non-`known` cell, which gives `unk`. `.` and `,` just copy cells.
2. **Soundness.** `aexecS_sound` is proved once for both rules, since it is parametric
   in the initial state. It says that if the abstract run from `a` ends in `r`, then the
   concrete run from any state that `a` describes ends on a tape that `r` describes.
3. **Computation.** For each organism, the abstract run of `P ++ [unk × 64]` is checked in
   16 chunks of 512 steps: `theorem chunkᵢ : aexecS 512 cpᵢ = some cpᵢ₊₁ := by decide +kernel`.
   The checkpoints `cpᵢ` are literals printed by `#eval`. They are **untrusted**: the
   kernel re-derives every chunk, so a wrong checkpoint fails the build. `aexecS_chain`
   composes the chunks into all 8192 steps. The last state is checked pointwise to be
   exactly `P ++ reverse P` or `P ++ P`.
4. **Concrete facts** (the collision, killers) use the same machinery on fully known
   tapes. `exact_concrete` then gives `run t = R` for a literal final tape `R`, and
   `ne_mirror` or `ne_copy` pick out a byte where `R` differs from the replicator's output.

## How the semantics match `bff.py`

Heads are `Fin 128`, so `h-1` and `h+1` wrap immediately. bff.py masks with `& 127` at
the top of the next iteration, and heads are only read after the mask, so the two behave
identically. A halt is encoded as `pos := 128`. That covers the `[` no-match case, and
the `]` no-match case where bff.py returns immediately (`]` doesn't write, so the tape is
the same). The bracket scans are transcribed with their depth updates in bff.py's order.

`CheckPOL.lean` compares the interpreters with `bff.py` on 240 tapes each:
**`run` 240/240, `runHeads` 240/240.** The tapes cover all three ways to halt, head
wraparound in both directions, byte overflow and underflow, and bracket jumps both
matched and unmatched. As an extra consistency check, the concrete final tapes in the
certificates match `bff.py`:
- the collision output;
- both parent-killer tapes;
- all 8 killer tapes, which also equal `killer_child` in `data/killers.json`.

This faithfulness is established by review and testing, **not proved**. The theorems are
about the Lean `run` and `runHeads`.

## Reproducing

```sh
cd lean
python3 gen_atlas.py            # checkpoints via #eval; writes ProofOfLife/Organisms/*, Birth52/*
./build_timed.sh 8 ProofOfLife.Abstract ProofOfLife.Birth52.Data -- $(cat gen/phaseA.txt)
./build_timed.sh 8 -- $(cat gen/phaseB.txt)     # lineage modules, World50Killer, Certificate
lake build                      # everything, including Atlas
lake env lean Atlas.lean        # #print axioms of every main theorem
python3 make_report.py          # atlas_report.json
lake env lean CheckPOL.lean     # bff.py cross-check
```

---

# Appendix: MirrorLife (the original world-30 proof)

This is a Lean 4 proof that the 64-byte program from world 30 of the `bff_noheads` soup
(`web/data/atlas.json`, `noheads`, `"seed": 30`, field `rep`) writes its mirror image
into **every** possible 64-byte partner. That covers all 256^64 partners.

## Theorem (`MirrorLife.lean`)

```lean
def run (t : Tape) : Tape := exec 8192 ⟨t, 0, 0, 0⟩      -- Tape := Vector UInt8 128

theorem mirror_copy (B : Vector UInt8 64) : run (P ++ B) = P ++ P.reverse
```

`P : Vector UInt8 64` is the genome, written out as bytes. `run` is the concrete BFF
interpreter with `bff_noheads` semantics: pos = h0 = h1 = 0, at most 8192 steps, halting
when pos ≥ 128 or when a bracket has no match.

## What is checked, and how

| Part | Name | Checked by |
|---|---|---|
| Concrete interpreter | `scanFwd`, `scanBwd`, `stepOp`, `step`, `exec`, `run` | definitions |
| Abstract interpreter on `Option UInt8` cells (`none` = unknown partner byte) | `astepOp`, `astep`, `aexec`, `aexecS` | definitions |
| Soundness: if the abstract run succeeds, every concrete tape that agrees with it on known cells ends on a tape that agrees with the abstract result | `aexec_sound` (and scan and step lemmas) | kernel, ordinary proof |
| Abstract run of `P ++ [unknown × 64]` for 8192 steps succeeds and ends fully known as `P ++ reverse P` | `abstract_run` | **kernel computation (`decide +kernel`)** |
| Main theorem | `mirror_copy` | kernel, ordinary proof |

The abstract interpreter gives up (`none`) whenever the concrete behaviour would depend
on an unknown cell. That means fetching an unknown opcode, testing an unknown byte in
`[` or `]`, or a bracket scan crossing an unknown cell. `+`, `-`, `.` and `,` on unknown
cells just move or produce "unknown". Because the abstract run succeeds, P never
depends on its partner's bytes.

**No `native_decide`, no `sorry`, no `admit`, no new axioms.** `#print axioms mirror_copy`
reports only `[propext, Quot.sound]`, which are Lean's standard axioms. `Lean.ofReduceBool`
does not appear, so no compiled code is trusted.

**Chunking.** Checking the whole run in one `decide +kernel` did not work in practice:

| Steps in one `decide +kernel` | Result |
|---|---|
| 2000 | about 17 s |
| 4000 | succeeded, but took about 51 min wall-clock (42 s user, 313 s sys, 1.5 GB peak RSS; another check was running at the same time) |
| 8192 | failed after about 60 min wall-clock with "maximum recursion depth has been reached" |

So the run is split into 16 chunks of 512 steps, about 5 s each. Chunk `i` is the kernel
check `aexecS 512 cpᵢ = some cpᵢ₊₁`, starting from an explicit literal state. The
checkpoints `cp1..cp16` were printed with `#eval`, but nothing about them is trusted:
the kernel re-derives every chunk, and a wrong checkpoint would fail to compile.
`aexecS_trans` composes the chunks. The final tape is compared pointwise
(`cp16_pointwise`, so the kernel never has to evaluate `Array.reverse`) and then turned
into `cp16.tape = expectedA` by a normal proof.

## How the semantics match `analysis/bff.py` `run` (and the `NAIVE` path of `engine/tol.c`)

- **Heads.** Heads are `Fin 128`, so `h-1` and `h+1` wrap immediately. bff.py masks
  with `& 127` at the top of the next iteration, and heads are only read after that
  mask, so the two behave identically.
- **Halting.** A halt is encoded as `pos := 128`, and `exec` stops when `pos ≥ 128`.
  That covers the `[` no-match case (bff.py sets pos = 128, then 129) and the `]`
  no-match case (bff.py returns immediately; `]` does not write, so the tape is the same).
- **Bracket scans.** `[` scans positions `pos+1..127`: first `]` decrements the depth,
  then `[` increments it. `]` scans `pos-1..0`: first `]` increments, then `[` decrements.
  After a jump, pos = match + 1.
- **Test vectors.** `run` has been cross-checked against bff.py on 240 tapes
  (`gen_vectors.py` → `test_vectors.txt`, checked in `Check.lean`): 20 copies of P with
  random partners, 40 uniformly random tapes, and 180 opcode-dense tapes. Together they
  cover all three ways to halt, head wraparound in both directions, byte overflow and
  underflow, and bracket jumps both matched and unmatched. **240/240 match.** This
  faithfulness is an empirical check, not a proof. The theorem is about the Lean `run`
  as defined.

## Checking it

```sh
cd lean
lake build                  # compiles MirrorLife.lean, including all kernel computations
lake env lean Check.lean    # bff.py cross-check and axiom report
```

Output (Lean 4.21.0, Apple Silicon laptop):

```
$ lake build
✔ [2/3] Built MirrorLife
Build completed successfully.
real 85,67

$ lake env lean Check.lean
240 / 240 tapes match bff.py
'MirrorLife.aexec_sound' depends on axioms: [propext, Quot.sound]
'MirrorLife.abstract_run' depends on axioms: [propext, Quot.sound]
'MirrorLife.mirror_copy' depends on axioms: [propext, Quot.sound]
```

Almost all of the ~86 s goes to the 16 kernel chunks, about 4–5 s each. The soundness
proofs take about 1 s.

## Files

- `MirrorLife.lean`: interpreters, soundness, checkpoints, theorem. Core Lean only; no Mathlib, Std or Batteries.
- `Check.lean`: cross-check against bff.py test vectors, plus `#print axioms`.
- `gen_vectors.py`, `test_vectors.txt`: test vectors produced by `analysis/bff.py`.

## A note on one comment

The header comment of `ProofOfLife/Abstract.lean` says "no axioms". It means no axioms beyond Lean's standard `propext` and `Quot.sound`, which `#print axioms` reports for every main theorem. The file is left unedited so that the published sources are byte-identical to the ones that were checked.
