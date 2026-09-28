/-
  ProofOfLife.Semantics — the concrete BFF interpreter (the specification).

  This is the only file a reader must check against the reference
  implementations (analysis/bff.py `run`, engine/tol.c `evaluate` NAIVE path).
  Two rules share one step function and differ only in the initial state:

  * `run`      — "noheads" (the Computational Life paper's rule):
                 pos = h0 = h1 = 0.
  * `runHeads` — "heads" (cubff's `bff` variant):
                 h0 = tape[0] % 128, h1 = tape[1] % 128, pos = 2.

  Both run at most 8192 iterations and halt when pos ≥ 128 or when a bracket
  has no match. Core Lean 4 only.
-/

namespace ProofOfLife

/-- A 128-byte tape. -/
abbrev Tape := Vector UInt8 128

/-- Bounds-checked read (every read in the interpreter is in bounds; the default
is never used — it only avoids carrying proofs through the bracket scans). -/
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

/-- Forward bracket scan (`[` case): examine positions `p, p+1, ..., p+n-1`;
return the position where the depth reaches 0, or `none`. Called with
`p = pos+1`, `n = 127 - pos`, i.e. positions `pos+1 .. 127`. -/
def scanFwd (t : Tape) : (n : Nat) → (p : Nat) → (d : Nat) → Option Nat
  | 0, _, _ => none
  | n+1, p, d =>
    let d' := fwdDepth (rd t p 0) d
    if d' = 0 then some p else scanFwd t n (p+1) d'

/-- Backward bracket scan (`]` case): examine positions `n-1, ..., 0`;
return the position where the depth reaches 0, or `none`. Called with `n = pos`. -/
def scanBwd (t : Tape) : (n : Nat) → (d : Nat) → Option Nat
  | 0, _ => none
  | n+1, d =>
    let d' := bwdDepth (rd t n 0) d
    if d' = 0 then some n else scanBwd t n d'

/-- Machine state. Heads live in `Fin 128`, so `h - 1` / `h + 1` wrap modulo 128
(bff.py masks with `& 127` at the top of the next iteration; heads are only read
after that mask, so wrapping immediately is observationally identical).
A state with `pos ≥ 128` is halted. -/
structure State where
  tape : Tape
  pos  : Nat
  h0   : Fin 128
  h1   : Fin 128

/-- Execute instruction `c` (the byte under the IP). Halting = `pos := 128`. -/
def stepOp (s : State) (c : UInt8) : State :=
  let t := s.tape
  let nx := s.pos + 1
  if c = 60 then { s with pos := nx, h0 := s.h0 - 1 }                          -- '<'
  else if c = 62 then { s with pos := nx, h0 := s.h0 + 1 }                     -- '>'
  else if c = 123 then { s with pos := nx, h1 := s.h1 - 1 }                    -- '{'
  else if c = 125 then { s with pos := nx, h1 := s.h1 + 1 }                    -- '}'
  else if c = 43 then { s with pos := nx, tape := put t s.h0 (get t s.h0 + 1) } -- '+'
  else if c = 45 then { s with pos := nx, tape := put t s.h0 (get t s.h0 - 1) } -- '-'
  else if c = 46 then { s with pos := nx, tape := put t s.h1 (get t s.h0) }     -- '.'
  else if c = 44 then { s with pos := nx, tape := put t s.h0 (get t s.h1) }     -- ','
  else if c = 91 then                                                           -- '['
    if get t s.h0 = 0 then
      match scanFwd t (127 - s.pos) (s.pos + 1) 1 with
      | some q => { s with pos := q + 1 }   -- jump to matching ']' then pos += 1
      | none   => { s with pos := 128 }     -- no match: halt
    else { s with pos := nx }
  else if c = 93 then                                                           -- ']'
    if get t s.h0 ≠ 0 then
      match scanBwd t s.pos 1 with
      | some q => { s with pos := q + 1 }   -- jump to matching '[' then pos += 1
      | none   => { s with pos := 128 }     -- no match: halt immediately
    else { s with pos := nx }
  else { s with pos := nx }                                                     -- no-op

/-- One interpreter iteration (only called when `pos < 128`). -/
def step (s : State) : State := stepOp s (rd s.tape s.pos 0)

/-- Run for at most `fuel` iterations; stop early when `pos ≥ 128`. -/
def exec : Nat → State → Tape
  | 0, s => s.tape
  | n+1, s => if s.pos < 128 then exec n (step s) else s.tape

/-- Initial head value in the heads rule: `b % 128`. -/
def hd (b : UInt8) : Fin 128 := ⟨b.toNat % 128, Nat.mod_lt _ (by decide)⟩

/-- noheads rule (paper): pos = h0 = h1 = 0, 8192 steps; final tape. -/
def run (t : Tape) : Tape := exec 8192 ⟨t, 0, 0, 0⟩

/-- heads rule (cubff `bff`): h0 = t[0] % 128, h1 = t[1] % 128, pos = 2. -/
def runHeads (t : Tape) : Tape := exec 8192 ⟨t, 2, hd t[0], hd t[1]⟩

end ProofOfLife
