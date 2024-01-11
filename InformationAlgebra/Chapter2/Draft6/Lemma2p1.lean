import Mathlib

import InformationAlgebra.Chapter2.Draft6.ValuationAlgebra


open ValuationAlgebra


namespace ValuationAlgebra


variable
  [DistribLattice D]
  {Φ : D → Type*}
  [ValuationAlgebra Φ]
  {x y : D}
  (φ : Φ x)


theorem proof_2p1p2
    (p : z ≤ x)
    :
    (φ ⊗ ψ ⇓ z, le_trans p le_sup_left) = (φ ⊗ (ψ ⇓ x ⊓ y, inf_le_right) ⇓ z, le_trans p le_sup_left)
    := by
  rw [ValuationAlgebra.margin_trans]
  case y => exact x
  case p => exact p
  case q => exact le_sup_left
  rw [ValuationAlgebra.margin_mul]
  rw [←cast_margin_le_of_eq]
  case q => exact sup_inf_self.symm
  done


theorem proof_2p1p1
    :
    (φ ⊗ ψ ⇓ x ⊓ y, le_trans inf_le_left le_sup_left) = sup_idem↾ ((φ ⇓ x ⊓ y, inf_le_left) ⊗ (ψ ⇓ x ⊓ y, inf_le_right))
    := by
  rw [proof_2p1p2]
  case p => exact inf_le_left
  rw [ValuationAlgebra.mul_comm]
  rw [←cast_margin_le_of_eq]
  case p => exact le_sup_left
  rw [ValuationAlgebra.margin_mul]
  conv =>
    lhs; rhs; rhs
    tactic =>
      rw [cast_margin_eq_of_le]
      case z => exact x ⊓ y
      case q => rw [inf_comm, inf_assoc, inf_idem, inf_comm]
  rw [ValuationAlgebra.mul_comm]
  simp only [cast_trans, cast_mul_left]
  case q => exact sup_comm
  done


private theorem proof_2p1p3_lemma {z : D} (p : x ≤ z) (q : z ≤ x ⊔ y) : x ⊔ (y ⊓ z) = z := by
  rw [sup_inf_left]
  conv =>
    lhs; rhs
    tactic =>
      rw [sup_eq_right]
      exact p
  exact inf_eq_right.mpr q
  done


section
variable (z : D) [DistribLattice D]
#check castSymmRight (proof_2p1p1 (φ ⊗ ψ) (e z))
end


theorem proof_2p1p3
    (p : x ≤ z)
    (q : z ≤ x ⊔ y)
    :
    (φ ⊗ ψ ⇓ z, q) = (proof_2p1p3_lemma p q)↾ (φ ⊗ (ψ ⇓ y ⊓ z, inf_le_left))
    := by
  rw [ValuationAlgebra.mul_one (φ ⊗ ψ ⇓ z, _)]
  rw [←ValuationAlgebra.margin_refl (e z)]
  rw [cast_margin_eq_of_le (φ ⊗ ψ)]
  case z => exact (x ⊔ y) ⊓ z
  case q => exact inf_eq_right.mpr q
  rw [cast_mul_left, cast_trans]
  rw [cast_margin_eq_of_le (e z)]
  case z => exact (x ⊔ y) ⊓ z
  case q => exact inf_eq_right.mpr q
  rw [cast_mul_right, cast_trans]
  apply cast_symm_right
  case p => exact (proof_2p1p3_lemma p q).symm
  rw [cast_trans]
  rw [←(castSymmRight )]
  --   -- wow this is long
  --   rw [cast_margin_eq_of_le]
  --   case z => exact z
  --   case q => exact right_eq_inf.mpr q
  --   rw [cast_trans]
  --   rw [←ValuationAlgebra.mul_assoc]
  --   rw [proof_2p1p2 (φ ⊗ ψ) (e z)]

  done
