/-
  MirrorLife: a machine-checked proof that the 64-byte BFF program that emerged
  in world 30 of the `bff_noheads` soup copies itself mirror-reversed into ANY
  64-byte partner.

  Core Lean 4 only (no Mathlib / Std / Batteries).

  Structure
  1. `step` / `exec` / `run`   : concrete BFF interpreter (bff_noheads semantics).
  2. `astep` / `aexec`         : abstract interpreter on cells `Option UInt8`
                                 (`none` = unknown partner byte); it gives up
                                 (returns `none`) whenever the concrete behaviour
                                 would depend on an unknown cell.
  3. `aexec_sound`             : generic soundness theorem (kernel-checked).
  4. `abstract_run`            : the abstract run of `P ++ [unknown x 64]`
                                 succeeds and yields `P ++ reverse P`
                                 (checked by kernel computation, `decide +kernel`,
                                 in 16 chunks of 512 steps).
  5. `mirror_copy`             : the ∀-theorem over all 256^64 partners.
-/

namespace MirrorLife

/-! ## 1. Concrete interpreter -/

/-- A 128-byte tape. -/
abbrev Tape := Vector UInt8 128

/-- Bounds-checked read (all reads in the interpreter are in bounds; the
default is never used — it only avoids carrying proofs through the scans). -/
@[inline] def rd {α : Type} (t : Vector α 128) (p : Nat) (dflt : α) : α :=
  if h : p < 128 then t[p] else dflt

/-- Read at a head position. -/
@[inline] def get {α : Type} (t : Vector α 128) (i : Fin 128) : α := t[i.val]'i.isLt

/-- Write at a head position. -/
@[inline] def put {α : Type} (t : Vector α 128) (i : Fin 128) (v : α) : Vector α 128 :=
  t.set i.val v i.isLt

/-- Depth update of the forward scan at a cell holding `c`
(bff.py: `if t[pos] == 93: d -= 1` then `if t[pos] == 91: d += 1`). -/
def fwdDepth (c : UInt8) (d : Nat) : Nat :=
  let d := if c = 93 then d - 1 else d
  if c = 91 then d + 1 else d

/-- Depth update of the backward scan at a cell holding `c`
(bff.py: `if t[pos] == 93: d += 1` then `if t[pos] == 91: d -= 1`). -/
def bwdDepth (c : UInt8) (d : Nat) : Nat :=
  let d := if c = 93 then d + 1 else d
  if c = 91 then d - 1 else d

/-- Forward bracket scan (the `[` case): examine positions `p, p+1, ..., p+n-1`
starting with depth `d`; at each position first `]` decrements, then `[`
increments; return the position where the depth reaches 0, or `none` if it
never does. Called with `p = pos+1`, `n = 127 - pos`, i.e. positions
`pos+1 .. 127`, exactly like `while pos < 128 and d > 0` in bff.py. -/
def scanFwd (t : Tape) : (n : Nat) → (p : Nat) → (d : Nat) → Option Nat
  | 0, _, _ => none
  | n+1, p, d =>
    let d' := fwdDepth (rd t p 0) d
    if d' = 0 then some p else scanFwd t n (p+1) d'

/-- Backward bracket scan (the `]` case): examine positions `n-1, n-2, ..., 0`
starting with depth `d`; at each position first `]` increments, then `[`
decrements; return the position where the depth reaches 0, or `none`.
Called with `n = pos`, i.e. positions `pos-1 .. 0`. -/
def scanBwd (t : Tape) : (n : Nat) → (d : Nat) → Option Nat
  | 0, _ => none
  | n+1, d =>
    let d' := bwdDepth (rd t n 0) d
    if d' = 0 then some n else scanBwd t n d'

/-- Machine state. Heads live in `Fin 128`, so `h - 1` / `h + 1` wrap modulo
128. (bff.py lets a head go to -1 or 128 and masks it with `& 127` at the top of
the next iteration; heads are only ever read after that mask, so wrapping
immediately is observationally identical.) A state with `pos ≥ 128` is halted. -/
structure State where
  tape : Tape
  pos  : Nat
  h0   : Fin 128
  h1   : Fin 128

/-- Execute the instruction `c` (= the byte under the IP) in state `s`.
Halting is encoded by setting `pos` to 128. -/
def stepOp (s : State) (c : UInt8) : State :=
  let t := s.tape
  let nx := s.pos + 1
  if c = 60 then { s with pos := nx, h0 := s.h0 - 1 }                     -- '<'
  else if c = 62 then { s with pos := nx, h0 := s.h0 + 1 }                -- '>'
  else if c = 123 then { s with pos := nx, h1 := s.h1 - 1 }               -- '{'
  else if c = 125 then { s with pos := nx, h1 := s.h1 + 1 }               -- '}'
  else if c = 43 then { s with pos := nx, tape := put t s.h0 (get t s.h0 + 1) } -- '+'
  else if c = 45 then { s with pos := nx, tape := put t s.h0 (get t s.h0 - 1) } -- '-'
  else if c = 46 then { s with pos := nx, tape := put t s.h1 (get t s.h0) }     -- '.'
  else if c = 44 then { s with pos := nx, tape := put t s.h0 (get t s.h1) }     -- ','
  else if c = 91 then                                                      -- '['
    if get t s.h0 = 0 then
      match scanFwd t (127 - s.pos) (s.pos + 1) 1 with
      | some q => { s with pos := q + 1 }      -- jump to matching ']' then pos += 1
      | none   => { s with pos := 128 }        -- no match: halt
    else { s with pos := nx }
  else if c = 93 then                                                      -- ']'
    if get t s.h0 ≠ 0 then
      match scanBwd t s.pos 1 with
      | some q => { s with pos := q + 1 }      -- jump to matching '[' then pos += 1
      | none   => { s with pos := 128 }        -- no match: halt immediately
    else { s with pos := nx }
  else { s with pos := nx }                                                -- no-op

/-- One interpreter iteration (only called when `pos < 128`). -/
def step (s : State) : State := stepOp s (rd s.tape s.pos 0)

/-- Run for at most `fuel` iterations; stop early when `pos ≥ 128`. -/
def exec : Nat → State → Tape
  | 0, s => s.tape
  | n+1, s => if s.pos < 128 then exec n (step s) else s.tape

/-- bff_noheads: pos = h0 = h1 = 0, 8192 steps; returns the final tape. -/
def run (t : Tape) : Tape := exec 8192 ⟨t, 0, 0, 0⟩

/-! ## 2. Abstract interpreter over `Option UInt8` cells -/

abbrev ATape := Vector (Option UInt8) 128

/-- Abstract forward scan: outer `none` = gave up (hit an unknown cell);
`some r` = the concrete scan returns `r`. -/
def ascanFwd (a : ATape) : (n : Nat) → (p : Nat) → (d : Nat) → Option (Option Nat)
  | 0, _, _ => some none
  | n+1, p, d =>
    match rd a p none with
    | none => none
    | some c =>
      let d' := fwdDepth c d
      if d' = 0 then some (some p) else ascanFwd a n (p+1) d'

def ascanBwd (a : ATape) : (n : Nat) → (d : Nat) → Option (Option Nat)
  | 0, _ => some none
  | n+1, d =>
    match rd a n none with
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
  else if c = 43 then some { s with pos := nx, tape := put t s.h0 ((get t s.h0).map (· + 1)) }
  else if c = 45 then some { s with pos := nx, tape := put t s.h0 ((get t s.h0).map (· - 1)) }
  else if c = 46 then some { s with pos := nx, tape := put t s.h1 (get t s.h0) }
  else if c = 44 then some { s with pos := nx, tape := put t s.h0 (get t s.h1) }
  else if c = 91 then
    match get t s.h0 with
    | none => none
    | some v =>
      if v = 0 then
        match ascanFwd t (127 - s.pos) (s.pos + 1) 1 with
        | none => none
        | some (some q) => some { s with pos := q + 1 }
        | some none => some { s with pos := 128 }
      else some { s with pos := nx }
  else if c = 93 then
    match get t s.h0 with
    | none => none
    | some v =>
      if v ≠ 0 then
        match ascanBwd t s.pos 1 with
        | none => none
        | some (some q) => some { s with pos := q + 1 }
        | some none => some { s with pos := 128 }
      else some { s with pos := nx }
  else some { s with pos := nx }

/-- Abstract step: gives up if the opcode under the IP is unknown. -/
def astep (s : AState) : Option AState :=
  match rd s.tape s.pos none with
  | none => none
  | some c => astepOp s c

def aexec : Nat → AState → Option ATape
  | 0, s => some s.tape
  | n+1, s =>
    if s.pos < 128 then
      match astep s with
      | none => none
      | some s' => aexec n s'
    else some s.tape

/-- Abstract run returning the whole final state (used to split the big
computation into chunks that start from explicit, fully evaluated states). -/
def aexecS : Nat → AState → Option AState
  | 0, s => some s
  | n+1, s =>
    if s.pos < 128 then
      match astep s with
      | none => none
      | some s' => aexecS n s'
    else some s

/-! ## 3. Soundness -/

/-- Concrete tape `t` agrees with abstract tape `a` on every known cell of `a`. -/
def Agrees (t : Tape) (a : ATape) : Prop :=
  ∀ i : Fin 128, ∀ v, get a i = some v → get t i = v

/-- Simulation relation between concrete and abstract states. -/
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

theorem rd_sound {t : Tape} {a : ATape} (h : Agrees t a) {p : Nat} {v : UInt8}
    (hr : rd a p none = some v) : rd t p 0 = v := by
  unfold rd at *
  split at hr
  · rename_i hp
    simp only [hp, dite_true]
    exact h ⟨p, hp⟩ v hr
  · cases hr

theorem agrees_put {t : Tape} {a : ATape} (h : Agrees t a) (i : Fin 128)
    (w : UInt8) (x : Option UInt8) (hx : ∀ v, x = some v → w = v) :
    Agrees (put t i w) (put a i x) := by
  intro j v hj
  rw [get_put] at hj ⊢
  by_cases hij : i = j
  · simp only [hij, if_true] at hj ⊢
    exact hx v hj
  · simp only [hij, if_false] at hj ⊢
    exact h j v hj

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
    refine ⟨rfl, rfl, rfl, agrees_put ht _ _ _ ?_⟩
    intro v hv
    cases hg : get a_tape s_h0 with
    | none => simp [hg] at hv
    | some u =>
      simp [hg] at hv
      rw [ht s_h0 u hg, hv]
  simp only [c43, if_false] at h ⊢
  by_cases c45 : c = 45
  · simp only [c45, if_true] at h ⊢; cases h
    refine ⟨rfl, rfl, rfl, agrees_put ht _ _ _ ?_⟩
    intro v hv
    cases hg : get a_tape s_h0 with
    | none => simp [hg] at hv
    | some u =>
      simp [hg] at hv
      rw [ht s_h0 u hg, hv]
  simp only [c45, if_false] at h ⊢
  by_cases c46 : c = 46
  · simp only [c46, if_true] at h ⊢; cases h
    exact ⟨rfl, rfl, rfl, agrees_put ht _ _ _ (fun v hv => ht s_h0 v hv)⟩
  simp only [c46, if_false] at h ⊢
  by_cases c44 : c = 44
  · simp only [c44, if_true] at h ⊢; cases h
    exact ⟨rfl, rfl, rfl, agrees_put ht _ _ _ (fun v hv => ht s_h1 v hv)⟩
  simp only [c44, if_false] at h ⊢
  by_cases c91 : c = 91
  · simp only [c91, if_true] at h ⊢
    split at h
    · cases h
    · rename_i v hv
      have hv' := ht s_h0 v hv
      rw [hv']
      split at h
      · rename_i hz
        rw [if_pos hz]
        split at h
        · cases h
        · rename_i q hq
          have := scanFwd_sound ht _ _ _ _ hq
          rw [this]; cases h; exact ⟨rfl, rfl, rfl, ht⟩
        · rename_i hq
          have := scanFwd_sound ht _ _ _ _ hq
          rw [this]; cases h; exact ⟨rfl, rfl, rfl, ht⟩
      · rename_i hz
        rw [if_neg hz]
        cases h; exact ⟨rfl, rfl, rfl, ht⟩
  simp only [c91, if_false] at h ⊢
  by_cases c93 : c = 93
  · simp only [c93, if_true] at h ⊢
    split at h
    · cases h
    · rename_i v hv
      have hv' := ht s_h0 v hv
      rw [hv']
      split at h
      · rename_i hz
        rw [if_pos hz]
        split at h
        · cases h
        · rename_i q hq
          have := scanBwd_sound ht _ _ _ hq
          rw [this]; cases h; exact ⟨rfl, rfl, rfl, ht⟩
        · rename_i hq
          have := scanBwd_sound ht _ _ _ hq
          rw [this]; cases h; exact ⟨rfl, rfl, rfl, ht⟩
      · rename_i hz
        rw [if_neg hz]
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

/-- **Soundness.** If the abstract run succeeds, the concrete run from any
related state ends on a tape that agrees with the abstract result. -/
theorem aexec_sound : ∀ (n : Nat) (s : State) (a : AState) (r : ATape),
    Rel s a → aexec n a = some r → Agrees (exec n s) r := by
  intro n
  induction n with
  | zero =>
    intro s a r hr h
    simp only [aexec, Option.some.injEq] at h
    subst h
    exact hr.2.2.2
  | succ n ih =>
    intro s a r hr h
    unfold aexec at h
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

theorem aexec_eq_aexecS : ∀ (n : Nat) (s : AState),
    aexec n s = (aexecS n s).map AState.tape := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    unfold aexec aexecS
    split
    · split
      · rfl
      · exact ih _
    · rfl

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

/-! ## 4. The program and the computation -/

/-- The world-30 replicator (atlas.json, noheads, seed 30, field `rep`). -/
def P : Vector UInt8 64 := #v[
  0x82, 0x49, 0x5b, 0xe5, 0x0c, 0x04, 0xe2, 0x5b, 0x46, 0x3d, 0x44, 0x3c, 0xe2, 0x08, 0x2c, 0x45,
  0x39, 0xff, 0x28, 0xe3, 0x3d, 0x07, 0x26, 0x28, 0x01, 0x3d, 0x6c, 0x75, 0xa3, 0xff, 0x7d, 0x3a,
  0x57, 0x5d, 0x57, 0x3a, 0x7d, 0xff, 0xa3, 0x1b, 0x6c, 0x3d, 0x01, 0x28, 0x26, 0x07, 0x3d, 0xe3,
  0x28, 0xff, 0x39, 0x89, 0x2c, 0x08, 0xe2, 0x3c, 0x44, 0xb2, 0x46, 0x5b, 0xe2, 0x22, 0x3f, 0x41]

/-- Abstract initial tape: P known, the 64 partner cells unknown. -/
def initA : ATape := P.map some ++ Vector.replicate 64 (none : Option UInt8)

/-- Expected final tape, fully known. -/
def expectedA : ATape := (P ++ P.reverse).map some

/-! ### Checkpoints

The 8192-step abstract run is checked in 16 chunks of 512 steps. A single
`decide +kernel` over all 8192 steps failed ("maximum recursion depth has been
reached") after ~60 min wall-clock; a single 4000-step `decide +kernel` did
succeed but took ~51 min wall-clock (42 s user, 313 s sys, 1.5 GB peak RSS,
measured while another check ran concurrently); 2000 steps took ~17 s. Restarting
every 512 steps from an explicit literal state keeps each chunk at ~5 s. The
checkpoint states `cp1 .. cp16` below were printed by
`#eval` (see README). Nothing about them is trusted: every chunk equation
`aexecS 512 cpᵢ = some cpᵢ₊₁` is re-checked by the kernel (`decide +kernel`),
so a wrong checkpoint would make the file fail to compile. -/

/-- Checkpoint 0: P known, partner unknown, pos = h0 = h1 = 0. -/
def cp0 : AState := ⟨initA, 0, 0, 0⟩

def cp1 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   18, 108, 19⟩

def cp2 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   10, 89, 39⟩

def cp3 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, none, none, none, none, none, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   28, 69, 58⟩

def cp4 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   20, 49, 78⟩

def cp5 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   12, 29, 98⟩

def cp6 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   30, 10, 117⟩

def cp7 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   22, 118, 9⟩

def cp8 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   14, 98, 29⟩

def cp9 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   32, 79, 49⟩

def cp10 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   24, 59, 68⟩

def cp11 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   16, 39, 88⟩

def cp12 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   8, 20, 108⟩

def cp13 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   26, 0, 127⟩

def cp14 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   18, 108, 19⟩

def cp15 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   10, 89, 39⟩

def cp16 : AState :=
  ⟨#v[some 130, some 73, some 91, some 229, some 12, some 4, some 226, some 91, some 70, some 61, some 68, some 60, some 226, some 8, some 44, some 69, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 117, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 27, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 137, some 44, some 8, some 226, some 60, some 68, some 178, some 70, some 91, some 226, some 34, some 63, some 65, some 65, some 63, some 34, some 226, some 91, some 70, some 178, some 68, some 60, some 226, some 8, some 44, some 137, some 57, some 255, some 40, some 227, some 61, some 7, some 38, some 40, some 1, some 61, some 108, some 27, some 163, some 255, some 125, some 58, some 87, some 93, some 87, some 58, some 125, some 255, some 163, some 117, some 108, some 61, some 1, some 40, some 38, some 7, some 61, some 227, some 40, some 255, some 57, some 69, some 44, some 8, some 226, some 60, some 68, some 61, some 70, some 91, some 226, some 4, some 12, some 229, some 91, some 73, some 130],
   28, 69, 58⟩

theorem chunk0 : aexecS 512 cp0 = some cp1 := by decide +kernel
theorem chunk1 : aexecS 512 cp1 = some cp2 := by decide +kernel
theorem chunk2 : aexecS 512 cp2 = some cp3 := by decide +kernel
theorem chunk3 : aexecS 512 cp3 = some cp4 := by decide +kernel
theorem chunk4 : aexecS 512 cp4 = some cp5 := by decide +kernel
theorem chunk5 : aexecS 512 cp5 = some cp6 := by decide +kernel
theorem chunk6 : aexecS 512 cp6 = some cp7 := by decide +kernel
theorem chunk7 : aexecS 512 cp7 = some cp8 := by decide +kernel
theorem chunk8 : aexecS 512 cp8 = some cp9 := by decide +kernel
theorem chunk9 : aexecS 512 cp9 = some cp10 := by decide +kernel
theorem chunk10 : aexecS 512 cp10 = some cp11 := by decide +kernel
theorem chunk11 : aexecS 512 cp11 = some cp12 := by decide +kernel
theorem chunk12 : aexecS 512 cp12 = some cp13 := by decide +kernel
theorem chunk13 : aexecS 512 cp13 = some cp14 := by decide +kernel
theorem chunk14 : aexecS 512 cp14 = some cp15 := by decide +kernel
theorem chunk15 : aexecS 512 cp15 = some cp16 := by decide +kernel

/-- The 16 chunks compose into the full 8192-step abstract run. -/
theorem abstract_runS : aexecS 8192 cp0 = some cp16 := by
  have h := aexecS_trans _ _ _ _ _ chunk0 (aexecS_trans _ _ _ _ _ chunk1 (aexecS_trans _ _ _ _ _ chunk2 (aexecS_trans _ _ _ _ _ chunk3 (aexecS_trans _ _ _ _ _ chunk4 (aexecS_trans _ _ _ _ _ chunk5 (aexecS_trans _ _ _ _ _ chunk6 (aexecS_trans _ _ _ _ _ chunk7 (aexecS_trans _ _ _ _ _ chunk8 (aexecS_trans _ _ _ _ _ chunk9 (aexecS_trans _ _ _ _ _ chunk10 (aexecS_trans _ _ _ _ _ chunk11 (aexecS_trans _ _ _ _ _ chunk12 (aexecS_trans _ _ _ _ _ chunk13 (aexecS_trans _ _ _ _ _ chunk14 (chunk15)))))))))))))))
  simp only [Nat.reduceAdd] at h
  exact h

/-- Pointwise check of the last checkpoint (kernel computation). Stated
pointwise so the kernel never has to evaluate `Array.reverse`, which is defined
by well-founded recursion and reduces poorly in the kernel. -/
theorem cp16_pointwise : ∀ i (h : i < 128),
    cp16.tape[i] = if h' : i < 64 then some P[i] else some (P[127 - i]'(by omega)) := by
  decide +kernel

theorem cp16_tape : cp16.tape = expectedA := by
  apply Vector.ext
  intro i hi
  rw [cp16_pointwise i hi]
  unfold expectedA
  rw [Vector.getElem_map, Vector.getElem_append]
  by_cases h : i < 64
  · simp [h]
  · have e : 64 - 1 - (i - 64) = 127 - i := by omega
    simp [h, Vector.getElem_reverse, e]

/-- The abstract run succeeds and produces the fully known tape P ++ reverse P. -/
theorem abstract_run : aexec 8192 ⟨initA, 0, 0, 0⟩ = some expectedA := by
  rw [aexec_eq_aexecS]
  show Option.map AState.tape (aexecS 8192 cp0) = some expectedA
  rw [abstract_runS, ← cp16_tape]
  rfl

/-! ## 5. The theorem -/

theorem agrees_init (B : Vector UInt8 64) : Agrees (P ++ B) initA := by
  intro i v hv
  unfold get initA at *
  rw [Vector.getElem_append] at hv ⊢
  by_cases hi : i.val < 64
  · simp only [hi, dite_true, Vector.getElem_map, Option.some.injEq] at hv ⊢
    exact hv
  · simp only [hi, dite_false, Vector.getElem_replicate] at hv
    cases hv

/-- **Main theorem.** For every 64-byte partner `B`, running the tape `P ++ B`
under bff_noheads semantics for 8192 steps ends with the tape `P ++ reverse P`. -/
theorem mirror_copy (B : Vector UInt8 64) : run (P ++ B) = P ++ P.reverse := by
  have hA := aexec_sound 8192 ⟨P ++ B, 0, 0, 0⟩ ⟨initA, 0, 0, 0⟩ expectedA
    ⟨rfl, rfl, rfl, agrees_init B⟩ abstract_run
  apply Vector.ext
  intro i hi
  have := hA ⟨i, hi⟩ ((P ++ P.reverse)[i]) (by
    unfold get expectedA
    simp)
  exact this

end MirrorLife
