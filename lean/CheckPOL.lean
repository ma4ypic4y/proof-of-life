import ProofOfLife.Semantics

/-! Sanity check (not part of the proof): the ProofOfLife interpreters against
analysis/bff.py on the vectors from gen_vectors.py (noheads and heads=True). -/

open ProofOfLife

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def parseHex : List Char → List Nat
  | a :: b :: rest => (hexVal a * 16 + hexVal b) :: parseHex rest
  | _ => []

def mkTape (l : List Nat) : Tape := Vector.ofFn fun i => (l.getD i.val 0).toUInt8

def checkFile (f : Tape → Tape) (path : String) : IO Unit := do
  let s ← IO.FS.readFile path
  let lines := (s.splitOn "\n").filter (· ≠ "")
  let ok := lines.filter fun line =>
    let bytes := parseHex line.toList
    ((f (mkTape (bytes.take 128))).toList.map (·.toNat)) == bytes.drop 128
  IO.println s!"{path}: {ok.length} / {lines.length} tapes match bff.py"

#eval checkFile run "test_vectors.txt"
#eval checkFile runHeads "test_vectors_heads.txt"
