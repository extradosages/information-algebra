import InformationAlgebra.Chapter2.Draft6.Defs.Basic
import InformationAlgebra.Chapter2.Draft6.Defs.CastValuationAlgebra


open ValuationAlgebra
open ValuationAlgebra.GCastRefl
open CastValuationAlgebra


variable
  [DistribLattice D]
  {Φ : D → Type*}
  [CastValuationAlgebra Φ]
  {x y : D}
  (φ : Φ x)
  (ψ : Φ y)


open CastValuationAlgebra


theorem proof_2p1p2
    (p : z ≤ x)
    :
    (φ ⊗ ψ ⇓ z, le_trans p le_sup_left) = (φ ⊗ (ψ ⇓ x ⊓ y, inf_le_right) ⇓ z, le_trans p le_sup_left)
    := by
  rw [margin_trans]
  rw [margin_mul]
  rw [←cast_margin_le_of_eq]
  done

theorem proof_2p1p1
    :
    (φ ⊗ ψ ⇓ x ⊓ y, le_trans inf_le_left le_sup_left) = sup_idem↾ ((φ ⇓ x ⊓ y, inf_le_left) ⊗ (ψ ⇓ x ⊓ y, inf_le_right))
    := by
  rw [proof_2p1p2]
  rw [CastValuationAlgebra.mul_comm]
  rw [←cast_margin_le_of_eq]
  rw [margin_mul]
  rw [cast_symm, cast_trans]
  have h : x ⊓ y = x ⊓ y ⊓ x := by
    rw [inf_comm, inf_assoc, inf_idem]
    done
  rw [cast_margin_eq_of_le h]
  rw [cast_mul_right]
  rw [cast_symm, cast_trans]
  rw [CastValuationAlgebra.mul_comm]
  case p => exact inf_le_left
  done


theorem proof_2p1p3
    (p : z ≤ x ⊔ y)
    (q : x ≤ z)
    :
    (φ ⊗ ψ ⇓ z, p) = s↾ (φ ⊗ (ψ ⇓ y ⊓ z, inf_le_left))
    := by
  sorry
  done
