import Mathlib

import InformationAlgebra.Chapter2.Draft7.ValuationAlgebra


open ValuationAlgebra


variable
  {D : Type*}
  [DistribLattice D]
  {Φ : D → Type*}
  [GValuationAlgebra Φ]
  {x y : D}
  (φ : Φ x)
  (ψ : Φ y)


theorem proof_2p1p2 (q : z ≤ x) : (φ ⊗ ψ) ↓ (le_trans q sup_le_left) = (φ ⊗ (ψ ↓ (inf_le_right : x ⊓ y ≤ y)) ↓ q :=
  rw []
  done


theorem proof_2p1p1 : (φ ⊗ ψ) ↓ (x ⊓ y) = (φ ↓ x ⊓ y) ⊗ (ψ ↓ x ⊓ y) :=
  sorry
  done
