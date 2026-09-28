/-
  ProofOfLife.Abstract — abstract interpreter, soundness, chunking, and the
  generic lemmas every organism module instantiates.

  Abstract cells: `known v`, `unk` (any byte), `nz` (any NONZERO byte).
  The abstract run gives up (returns `none`) whenever the concrete behaviour
  could depend on what an `unk`/`nz` cell holds:
    * fetching a non-`known` opcode,
    * a bracket scan crossing a non-`known` cell,
    * `[` / `]` testing an `unk` cell (an `nz` cell counts as nonzero).
  `+`/`-` on non-`known` cells give `unk`; `.`/`,` copy cells unchanged.
  Everything here is proved in the kernel; no `native_decide`, no axioms.
-/
import ProofOfLife.Semantics

namespace ProofOfLife

/-! ## Abstract domain -/

inductive ACell where
  | known (v : UInt8)
  | unk
  | nz
  deriving DecidableEq, Repr

namespace ACell

/-- The byte, if known. -/
def val : ACell → Option UInt8
  | known v => some v
  | _ => none

/-- `some b` iff the zero test of the cell is determined (`b = (cell = 0)`). -/
def zeroTest : ACell → Option Bool
  | known v => some (decide (v = 0))
  | nz => some false
  | unk => none

def inc : ACell → ACell
  | known v => known (v + 1)
  | _ => unk

def dec : ACell → ACell
  | known v => known (v - 1)
  | _ => unk

end ACell

/-- Concrete byte `c` is described by abstract cell `a`. -/
def CellAgrees (c : UInt8) : ACell → Prop
  | .known v => c = v
  | .unk => True
  | .nz => c ≠ 0

abbrev ATape := Vector ACell 128

/-- Concrete tape `t` is described by abstract tape `a`. -/
def Agrees (t : Tape) (a : ATape) : Prop := ∀ i : Fin 128, CellAgrees (get t i) (get a i)

/-! ## Abstract interpreter -/

def ascanFwd (a : ATape) : (n : Nat) → (p : Nat) → (d : Nat) → Option (Option Nat)
  | 0, _, _ => some none
  | n+1, p, d =>
    match (rd a p .unk).val with
    | none => none
    | some c =>
      let d' := fwdDepth c d
      if d' = 0 then some (some p) else ascanFwd a n (p+1) d'

def ascanBwd (a : ATape) : (n : Nat) → (d : Nat) → Option (Option Nat)
  | 0, _ => some none
  | n+1, d =>
    match (rd a n .unk).val with
    | none => none
    | some c =>
      let d' := bwdDepth c d
      if d' = 0 then some (some n) else ascanBwd a n d'

structure AState where
  tape : ATape
  pos  : Nat
  h0   : Fin 128
  h1   : Fin 128
  deriving DecidableEq, Repr

def astepOp (s : AState) (c : UInt8) : Option AState :=
  let t := s.tape
  let nx := s.pos + 1
  if c = 60 then some { s with pos := nx, h0 := s.h0 - 1 }
  else if c = 62 then some { s with pos := nx, h0 := s.h0 + 1 }
  else if c = 123 then some { s with pos := nx, h1 := s.h1 - 1 }
  else if c = 125 then some { s with pos := nx, h1 := s.h1 + 1 }
  else if c = 43 then some { s with pos := nx, tape := put t s.h0 (get t s.h0).inc }
  else if c = 45 then some { s with pos := nx, tape := put t s.h0 (get t s.h0).dec }
  else if c = 46 then some { s with pos := nx, tape := put t s.h1 (get t s.h0) }
  else if c = 44 then some { s with pos := nx, tape := put t s.h0 (get t s.h1) }
  else if c = 91 then
    match (get t s.h0).zeroTest with
    | none => none
    | some true =>
      match ascanFwd t (127 - s.pos) (s.pos + 1) 1 with
      | none => none
      | some (some q) => some { s with pos := q + 1 }
      | some none => some { s with pos := 128 }
    | some false => some { s with pos := nx }
  else if c = 93 then
    match (get t s.h0).zeroTest with
    | none => none
    | some false =>
      match ascanBwd t s.pos 1 with
      | none => none
      | some (some q) => some { s with pos := q + 1 }
      | some none => some { s with pos := 128 }
    | some true => some { s with pos := nx }
  else some { s with pos := nx }

def astep (s : AState) : Option AState :=
  match (rd s.tape s.pos .unk).val with
  | none => none
  | some c => astepOp s c

/-- Abstract run, returning the final state. -/
def aexecS : Nat → AState → Option AState
  | 0, s => some s
  | n+1, s =>
    if s.pos < 128 then
      match astep s with
      | none => none
      | some s' => aexecS n s'
    else some s

/-! ## Soundness -/

def Rel (s : State) (a : AState) : Prop :=
  s.pos = a.pos ∧ s.h0 = a.h0 ∧ s.h1 = a.h1 ∧ Agrees s.tape a.tape

theorem get_put {α : Type} (t : Vector α 128) (i j : Fin 128) (v : α) :
    get (put t i v) j = if i = j then v else get t j := by
  unfold get put
  rw [Vector.getElem_set]
  by_cases h : i = j
  · subst h; simp
  · have : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h, this]

theorem val_sound {c : UInt8} {a : ACell} (h : CellAgrees c a) {v : UInt8}
    (hv : a.val = some v) : c = v := by
  cases a with
  | known w => simp [ACell.val] at hv; subst hv; exact h
  | unk => simp [ACell.val] at hv
  | nz => simp [ACell.val] at hv

theorem zeroTest_sound {c : UInt8} {a : ACell} (h : CellAgrees c a) {b : Bool}
    (hb : a.zeroTest = some b) : decide (c = 0) = b := by
  cases a with
  | known w =>
    simp only [ACell.zeroTest, Option.some.injEq] at hb
    subst hb; simp only [CellAgrees] at h; subst h; rfl
  | unk => simp [ACell.zeroTest] at hb
  | nz =>
    simp only [ACell.zeroTest, Option.some.injEq] at hb
    subst hb; simp only [CellAgrees] at h; simp [h]

theorem inc_sound {c : UInt8} {a : ACell} (h : CellAgrees c a) : CellAgrees (c + 1) a.inc := by
  cases a with
  | known w => simp only [CellAgrees] at h; subst h; rfl
  | unk => trivial
  | nz => trivial

theorem dec_sound {c : UInt8} {a : ACell} (h : CellAgrees c a) : CellAgrees (c - 1) a.dec := by
  cases a with
  | known w => simp only [CellAgrees] at h; subst h; rfl
  | unk => trivial
  | nz => trivial

theorem rd_sound {t : Tape} {a : ATape} (h : Agrees t a) {p : Nat} {v : UInt8}
    (hr : (rd a p .unk).val = some v) : rd t p 0 = v := by
  unfold rd at *
  split at hr
  · rename_i hp
    simp only [hp, dite_true]
    exact val_sound (h ⟨p, hp⟩) hr
  · simp [ACell.val] at hr

theorem agrees_put {t : Tape} {a : ATape} (h : Agrees t a) (i : Fin 128)
    (w : UInt8) (x : ACell) (hx : CellAgrees w x) : Agrees (put t i w) (put a i x) := by
  intro j
  rw [get_put, get_put]
  by_cases hij : i = j
  · simp only [hij, if_true]; exact hx
  · simp only [hij, if_false]; exact h j

theorem scanFwd_sound {t : Tape} {a : ATape} (h : Agrees t a) :
    ∀ (n p d : Nat) (r : Option Nat), ascanFwd a n p d = some r → scanFwd t n p d = r := by
  intro n
  induction n with
  | zero => intro p d r hr; simp [ascanFwd] at hr; simp [scanFwd, hr]
  | succ n ih =>
    intro p d r hr
    unfold ascanFwd at hr
    split at hr
    · cases hr
    · rename_i c hc
      have hc' := rd_sound h hc
      unfold scanFwd
      simp only [hc']
      by_cases hd : fwdDepth c d = 0
      · simp only [hd, if_true] at hr ⊢
        exact Option.some.inj hr
      · simp only [hd, if_false] at hr ⊢
        exact ih _ _ _ hr

theorem scanBwd_sound {t : Tape} {a : ATape} (h : Agrees t a) :
    ∀ (n d : Nat) (r : Option Nat), ascanBwd a n d = some r → scanBwd t n d = r := by
  intro n
  induction n with
  | zero => intro d r hr; simp [ascanBwd] at hr; simp [scanBwd, hr]
  | succ n ih =>
    intro d r hr
    unfold ascanBwd at hr
    split at hr
    · cases hr
    · rename_i c hc
      have hc' := rd_sound h hc
      unfold scanBwd
      simp only [hc']
      by_cases hd : bwdDepth c d = 0
      · simp only [hd, if_true] at hr ⊢
        exact Option.some.inj hr
      · simp only [hd, if_false] at hr ⊢
        exact ih _ _ hr

theorem stepOp_sound {s : State} {a a' : AState} (hr : Rel s a) (c : UInt8)
    (h : astepOp a c = some a') : Rel (stepOp s c) a' := by
  obtain ⟨s_tape, s_pos, s_h0, s_h1⟩ := s
  obtain ⟨a_tape, a_pos, a_h0, a_h1⟩ := a
  obtain ⟨hp, h0, h1, ht⟩ := hr
  subst hp h0 h1
  unfold astepOp at h
  unfold stepOp
  simp only at h ⊢
  by_cases c60 : c = 60
  · simp only [c60, if_true] at h ⊢; cases h; exact ⟨rfl, rfl, rfl, ht⟩
  simp only [c60, if_false] at h ⊢
  by_cases c62 : c = 62
  · simp only [c62, if_true] at h ⊢; cases h; exact ⟨rfl, rfl, rfl, ht⟩
  simp only [c62, if_false] at h ⊢
  by_cases c123 : c = 123
  · simp only [c123, if_true] at h ⊢; cases h; exact ⟨rfl, rfl, rfl, ht⟩
  simp only [c123, if_false] at h ⊢
  by_cases c125 : c = 125
  · simp only [c125, if_true] at h ⊢; cases h; exact ⟨rfl, rfl, rfl, ht⟩
  simp only [c125, if_false] at h ⊢
  by_cases c43 : c = 43
  · simp only [c43, if_true] at h ⊢; cases h
    exact ⟨rfl, rfl, rfl, agrees_put ht _ _ _ (inc_sound (ht s_h0))⟩
  simp only [c43, if_false] at h ⊢
  by_cases c45 : c = 45
  · simp only [c45, if_true] at h ⊢; cases h
    exact ⟨rfl, rfl, rfl, agrees_put ht _ _ _ (dec_sound (ht s_h0))⟩
  simp only [c45, if_false] at h ⊢
  by_cases c46 : c = 46
  · simp only [c46, if_true] at h ⊢; cases h
    exact ⟨rfl, rfl, rfl, agrees_put ht _ _ _ (ht s_h0)⟩
  simp only [c46, if_false] at h ⊢
  by_cases c44 : c = 44
  · simp only [c44, if_true] at h ⊢; cases h
    exact ⟨rfl, rfl, rfl, agrees_put ht _ _ _ (ht s_h1)⟩
  simp only [c44, if_false] at h ⊢
  by_cases c91 : c = 91
  · simp only [c91, if_true] at h ⊢
    split at h
    · cases h
    · rename_i hz
      have hz' := zeroTest_sound (ht s_h0) hz
      have : get s_tape s_h0 = 0 := of_decide_eq_true hz'
      rw [if_pos this]
      split at h
      · cases h
      · rename_i q hq
        rw [scanFwd_sound ht _ _ _ _ hq]; cases h; exact ⟨rfl, rfl, rfl, ht⟩
      · rename_i hq
        rw [scanFwd_sound ht _ _ _ _ hq]; cases h; exact ⟨rfl, rfl, rfl, ht⟩
    · rename_i hz
      have hz' := zeroTest_sound (ht s_h0) hz
      have : ¬ get s_tape s_h0 = 0 := of_decide_eq_false hz'
      rw [if_neg this]
      cases h; exact ⟨rfl, rfl, rfl, ht⟩
  simp only [c91, if_false] at h ⊢
  by_cases c93 : c = 93
  · simp only [c93, if_true] at h ⊢
    split at h
    · cases h
    · rename_i hz
      have hz' := zeroTest_sound (ht s_h0) hz
      have : get s_tape s_h0 ≠ 0 := of_decide_eq_false hz'
      rw [if_pos this]
      split at h
      · cases h
      · rename_i q hq
        rw [scanBwd_sound ht _ _ _ hq]; cases h; exact ⟨rfl, rfl, rfl, ht⟩
      · rename_i hq
        rw [scanBwd_sound ht _ _ _ hq]; cases h; exact ⟨rfl, rfl, rfl, ht⟩
    · rename_i hz
      have hz' := zeroTest_sound (ht s_h0) hz
      have : ¬ get s_tape s_h0 ≠ 0 := fun hne => hne (of_decide_eq_true hz')
      rw [if_neg this]
      cases h; exact ⟨rfl, rfl, rfl, ht⟩
  simp only [c93, if_false] at h ⊢
  cases h; exact ⟨rfl, rfl, rfl, ht⟩

theorem step_sound {s : State} {a a' : AState} (hr : Rel s a)
    (h : astep a = some a') : Rel (step s) a' := by
  unfold astep at h
  split at h
  · cases h
  · rename_i c hc
    have hc' : rd s.tape s.pos 0 = c := by
      rw [hr.1]; exact rd_sound hr.2.2.2 hc
    unfold step
    rw [hc']
    exact stepOp_sound hr c h

/-- **Soundness.** If the abstract run from `a` succeeds with final state `r`,
then for every concrete state related to `a` the concrete run ends on a tape
described by `r.tape`. -/
theorem aexecS_sound : ∀ (n : Nat) (s : State) (a r : AState),
    Rel s a → aexecS n a = some r → Agrees (exec n s) r.tape := by
  intro n
  induction n with
  | zero =>
    intro s a r hr h
    simp only [aexecS, Option.some.injEq] at h
    subst h
    exact hr.2.2.2
  | succ n ih =>
    intro s a r hr h
    unfold aexecS at h
    unfold exec
    rw [hr.1]
    split at h
    · rename_i hp
      simp only [hp, if_true]
      split at h
      · cases h
      · rename_i a' ha'
        exact ih _ _ _ (step_sound hr ha') h
    · rename_i hp
      simp only [hp, if_false]
      simp only [Option.some.injEq] at h
      subst h
      exact hr.2.2.2

/-! ## Chunking -/

theorem aexecS_halted (m : Nat) (s : AState) (h : ¬ s.pos < 128) : aexecS m s = some s := by
  cases m with
  | zero => rfl
  | succ m => unfold aexecS; rw [if_neg h]

theorem aexecS_trans : ∀ (n m : Nat) (a b c : AState),
    aexecS n a = some b → aexecS m b = some c → aexecS (n + m) a = some c := by
  intro n
  induction n with
  | zero =>
    intro m a b c h1 h2
    simp only [aexecS, Option.some.injEq] at h1
    subst h1
    rw [Nat.zero_add]; exact h2
  | succ n ih =>
    intro m a b c h1 h2
    rw [Nat.succ_add]
    unfold aexecS at h1 ⊢
    split at h1
    · rename_i hp
      rw [if_pos hp]
      split at h1
      · cases h1
      · rename_i a' _
        exact ih m a' b c h1 h2
    · rename_i hp
      rw [if_neg hp]
      simp only [Option.some.injEq] at h1
      subst h1
      rw [aexecS_halted m a hp] at h2
      exact h2

/-- Chain two chunks, with the step count given explicitly. -/
theorem aexecS_chain {n m k : Nat} {a b c : AState} (h1 : aexecS n a = some b)
    (h2 : aexecS m b = some c) (hk : n + m = k) : aexecS k a = some c := by
  subst hk; exact aexecS_trans n m a b c h1 h2

/-! ## Initial abstract tapes and target shapes -/

/-- Program `P` known, partner described by `Bab`. -/
@[irreducible] def liftP (P : Vector UInt8 64) (Bab : Vector ACell 64) : ATape := P.map ACell.known ++ Bab

/-- Fully unknown partner. -/
@[irreducible] def unk64 : Vector ACell 64 := Vector.replicate 64 ACell.unk

/-- A concrete partner `B` is described by an abstract partner `Bab`. -/
def PartnerOK (B : Vector UInt8 64) (Bab : Vector ACell 64) : Prop :=
  ∀ j (h : j < 64), CellAgrees B[j] Bab[j]

theorem partnerOK_unk64 (B : Vector UInt8 64) : PartnerOK B unk64 := by
  intro j h; unfold unk64; simp [CellAgrees]

theorem agrees_liftP {P B : Vector UInt8 64} {Bab : Vector ACell 64}
    (hB : PartnerOK B Bab) : Agrees (P ++ B) (liftP P Bab) := by
  intro i
  unfold get liftP
  rw [Vector.getElem_append, Vector.getElem_append]
  by_cases hi : i.val < 64
  · simp only [hi, dite_true, Vector.getElem_map, CellAgrees]
  · simp only [hi, dite_false]
    exact hB _ _

/-- A fully known tape. -/
@[irreducible] def liftT (t : Tape) : ATape := t.map ACell.known

theorem agrees_liftT (t : Tape) : Agrees t (liftT t) := by
  intro i; unfold get liftT; simp [CellAgrees]

/-- Abstract tape is exactly the mirror child `P ++ reverse P` (stated pointwise so
that the kernel never has to evaluate `Array.reverse`). -/
@[reducible] def IsMirrorOf (P : Vector UInt8 64) (t : ATape) : Prop :=
  ∀ i (h : i < 128), t[i] = if h' : i < 64 then ACell.known P[i] else ACell.known (P[127 - i]'(by omega))

/-- Abstract tape is exactly the forward copy `P ++ P`. -/
@[reducible] def IsCopyOf (P : Vector UInt8 64) (t : ATape) : Prop :=
  ∀ i (h : i < 128), t[i] = if h' : i < 64 then ACell.known P[i] else ACell.known (P[i - 64]'(by omega))

/-- Turn an `Agrees` fact with a fully determined abstract tape into equality. -/
theorem eq_of_agrees {t R : Tape} {a : ATape} (h : Agrees t a)
    (hR : ∀ i (hi : i < 128), a[i] = ACell.known R[i]) : t = R := by
  apply Vector.ext
  intro i hi
  have := h ⟨i, hi⟩
  unfold get at this
  simp only [hR i hi, CellAgrees] at this
  exact this

theorem mirror_target {P : Vector UInt8 64} {a : ATape} (hm : IsMirrorOf P a) :
    ∀ i (hi : i < 128), a[i] = ACell.known (P ++ P.reverse)[i] := by
  intro i hi
  rw [hm i hi, Vector.getElem_append]
  by_cases h : i < 64
  · simp [h]
  · have e : 64 - 1 - (i - 64) = 127 - i := by omega
    simp [h, Vector.getElem_reverse, e]

theorem copy_target {P : Vector UInt8 64} {a : ATape} (hm : IsCopyOf P a) :
    ∀ i (hi : i < 128), a[i] = ACell.known (P ++ P)[i] := by
  intro i hi
  rw [hm i hi, Vector.getElem_append]
  by_cases h : i < 64
  · simp [h]
  · simp [h]

/-! ## Generic organism-level theorems -/

/-- Initial abstract state, noheads rule. -/
def startNH (a : ATape) : AState := ⟨a, 0, 0, 0⟩

/-- Initial abstract state, heads rule (heads from the program's first two bytes). -/
def startH (P : Vector UInt8 64) (a : ATape) : AState := ⟨a, 2, hd P[0], hd P[1]⟩

theorem heads_init (P B : Vector UInt8 64) :
    (P ++ B)[0] = P[0] ∧ (P ++ B)[1] = P[1] := by
  constructor
  · rw [Vector.getElem_append, dif_pos (by decide)]
  · rw [Vector.getElem_append, dif_pos (by decide)]

/-- Exact mirror copy for every partner (noheads). -/
theorem exact_mirror {P : Vector UInt8 64} {r : AState}
    (hrun : aexecS 8192 (startNH (liftP P unk64)) = some r) (hm : IsMirrorOf P r.tape) :
    ∀ B : Vector UInt8 64, run (P ++ B) = P ++ P.reverse := by
  intro B
  unfold run
  have hA : Agrees (exec 8192 ⟨P ++ B, 0, 0, 0⟩) r.tape :=
    aexecS_sound 8192 ⟨P ++ B, 0, 0, 0⟩ (startNH (liftP P unk64)) r
      ⟨rfl, rfl, rfl, agrees_liftP (partnerOK_unk64 B)⟩ hrun
  exact eq_of_agrees hA (mirror_target hm)

/-- Exact forward copy for every partner (heads rule). -/
theorem exact_copy_heads {P : Vector UInt8 64} {r : AState}
    (hrun : aexecS 8192 (startH P (liftP P unk64)) = some r) (hm : IsCopyOf P r.tape) :
    ∀ B : Vector UInt8 64, runHeads (P ++ B) = P ++ P := by
  intro B
  have hi := heads_init P B
  unfold runHeads
  have hA : Agrees (exec 8192 ⟨P ++ B, 2, hd (P ++ B)[0], hd (P ++ B)[1]⟩) r.tape :=
    aexecS_sound 8192 ⟨P ++ B, 2, hd (P ++ B)[0], hd (P ++ B)[1]⟩ (startH P (liftP P unk64)) r
      ⟨rfl, show hd (P ++ B)[0] = hd P[0] by rw [hi.1],
       show hd (P ++ B)[1] = hd P[1] by rw [hi.2],
       agrees_liftP (partnerOK_unk64 B)⟩ hrun
  exact eq_of_agrees hA (copy_target hm)

/-- Exact mirror copy for every partner described by `Bab` (noheads). -/
theorem guarded_mirror {P : Vector UInt8 64} {Bab : Vector ACell 64} {r : AState}
    (hrun : aexecS 8192 (startNH (liftP P Bab)) = some r) (hm : IsMirrorOf P r.tape) :
    ∀ B : Vector UInt8 64, PartnerOK B Bab → run (P ++ B) = P ++ P.reverse := by
  intro B hB
  unfold run
  have hA : Agrees (exec 8192 ⟨P ++ B, 0, 0, 0⟩) r.tape :=
    aexecS_sound 8192 ⟨P ++ B, 0, 0, 0⟩ (startNH (liftP P Bab)) r
      ⟨rfl, rfl, rfl, agrees_liftP hB⟩ hrun
  exact eq_of_agrees hA (mirror_target hm)

/-- A fully known run determines each output byte (noheads). -/
theorem concrete_byte {t : Tape} {r : AState}
    (hrun : aexecS 8192 (startNH (liftT t)) = some r) (i : Nat) (hi : i < 128)
    (v : UInt8) (hv : r.tape[i] = ACell.known v) : (run t)[i] = v := by
  unfold run
  have hA : Agrees (exec 8192 ⟨t, 0, 0, 0⟩) r.tape :=
    aexecS_sound 8192 ⟨t, 0, 0, 0⟩ (startNH (liftT t)) r ⟨rfl, rfl, rfl, agrees_liftT t⟩ hrun
  have := hA ⟨i, hi⟩
  unfold get at this
  simp only [hv, CellAgrees] at this
  exact this

/-- A fully known run determines each output byte (heads rule). -/
theorem concrete_byte_heads {t : Tape} {r : AState}
    (hrun : aexecS 8192 ⟨liftT t, 2, hd t[0], hd t[1]⟩ = some r) (i : Nat) (hi : i < 128)
    (v : UInt8) (hv : r.tape[i] = ACell.known v) : (runHeads t)[i] = v := by
  unfold runHeads
  have hA : Agrees (exec 8192 ⟨t, 2, hd t[0], hd t[1]⟩) r.tape :=
    aexecS_sound 8192 ⟨t, 2, hd t[0], hd t[1]⟩ ⟨liftT t, 2, hd t[0], hd t[1]⟩ r
      ⟨rfl, rfl, rfl, agrees_liftT t⟩ hrun
  have := hA ⟨i, hi⟩
  unfold get at this
  simp only [hv, CellAgrees] at this
  exact this

/-- Reversal bookkeeping for lineage theorems: if `Q` is `P` reversed
(checked pointwise), then `Q = P.reverse` and `Q.reverse = P`. -/
theorem rev_of_pointwise {P Q : Vector UInt8 64}
    (h : ∀ i (hi : i < 64), Q[i] = P[63 - i]'(by omega)) : Q = P.reverse := by
  apply Vector.ext
  intro i hi
  rw [h i hi, Vector.getElem_reverse]

/-! ## Concrete runs certified through the (fully known) abstract run -/

/-- Exact concrete result of a run (noheads) from a fully known abstract run. -/
theorem exact_concrete {t R : Tape} {r : AState}
    (hrun : aexecS 8192 (startNH (liftT t)) = some r)
    (hR : ∀ i (hi : i < 128), r.tape[i] = ACell.known R[i]) : run t = R := by
  unfold run
  have hA : Agrees (exec 8192 ⟨t, 0, 0, 0⟩) r.tape :=
    aexecS_sound 8192 ⟨t, 0, 0, 0⟩ (startNH (liftT t)) r ⟨rfl, rfl, rfl, agrees_liftT t⟩ hrun
  exact eq_of_agrees hA hR

/-- Exact concrete result of a run (heads rule) from a fully known abstract run. -/
theorem exact_concrete_heads {t R : Tape} {r : AState}
    (hrun : aexecS 8192 ⟨liftT t, 2, hd t[0], hd t[1]⟩ = some r)
    (hR : ∀ i (hi : i < 128), r.tape[i] = ACell.known R[i]) : runHeads t = R := by
  unfold runHeads
  have hA : Agrees (exec 8192 ⟨t, 2, hd t[0], hd t[1]⟩) r.tape :=
    aexecS_sound 8192 ⟨t, 2, hd t[0], hd t[1]⟩ ⟨liftT t, 2, hd t[0], hd t[1]⟩ r
      ⟨rfl, rfl, rfl, agrees_liftT t⟩ hrun
  exact eq_of_agrees hA hR

/-- Byte `i` of `P ++ P.reverse`, without evaluating `reverse`. -/
theorem mirror_getElem (P : Vector UInt8 64) (i : Nat) (hi : i < 128) :
    (P ++ P.reverse)[i] = if h' : i < 64 then P[i] else P[127 - i]'(by omega) := by
  rw [Vector.getElem_append]
  by_cases h : i < 64
  · simp [h]
  · have e : 64 - 1 - (i - 64) = 127 - i := by omega
    simp [h, Vector.getElem_reverse, e]

/-- Byte `i` of `P ++ P`. -/
theorem copy_getElem (P : Vector UInt8 64) (i : Nat) (hi : i < 128) :
    (P ++ P)[i] = if h' : i < 64 then P[i] else P[i - 64]'(by omega) := by
  rw [Vector.getElem_append]

/-- A tape differing from the mirror child at byte `i` is not the mirror child. -/
theorem ne_mirror {t : Tape} {P : Vector UInt8 64} (i : Nat) (hi : i < 128)
    (h : t[i] ≠ if h' : i < 64 then P[i] else P[127 - i]'(by omega)) : t ≠ P ++ P.reverse := by
  intro e; apply h; rw [e, mirror_getElem P i hi]

/-- A tape differing from the forward copy at byte `i` is not the forward copy. -/
theorem ne_copy {t : Tape} {P : Vector UInt8 64} (i : Nat) (hi : i < 128)
    (h : t[i] ≠ if h' : i < 64 then P[i] else P[i - 64]'(by omega)) : t ≠ P ++ P := by
  intro e; apply h; rw [e, copy_getElem P i hi]

end ProofOfLife
