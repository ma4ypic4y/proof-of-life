import ProofOfLife.Birth52.Certificate
open ProofOfLife ProofOfLife.Birth52 in
#check (birth_certificate_world52 :
    run (A ++ B) = A_out ++ C ∧
    (∀ X : Vector UInt8 64, run (C ++ X) = C ++ C.reverse) ∧
    (∀ X : Vector UInt8 64, run (C.reverse ++ X) = C.reverse ++ C) ∧
    (run (A ++ killer_A) ≠ A ++ A.reverse ∧ run (A ++ killer_A) ≠ A ++ A) ∧
    (run (B ++ killer_B) ≠ B ++ B.reverse ∧ run (B ++ killer_B) ≠ B ++ B))
#print axioms ProofOfLife.Birth52.birth_certificate_world52
