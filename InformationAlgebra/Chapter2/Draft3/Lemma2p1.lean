import Mathlib

import InformationAlgebra.Chapter2.Draft3.ValuationAlgebras


open ValuationAlgebras


variable
  {Φ : D → Type*}
  [DistribLattice D]
  [ValuationAlgebra Φ]
  (φ : Φ x)
  (ψ : Φ y)


private lemma lattice₁ (p : x ≤ z) : x ⊔ (y ⊓ z) ≤ z := by
  rw [sup_le_iff]
  apply And.intro
  case left => exact p
  case right => exact inf_le_right
  done


private def Statement2p1p3 (z : SubDomain (x ⊔ y)) (p : x ≤ z) : Prop :=
  let ϕ := φ * (ψ ↓ (y ⊓ z : D))
  let ϕ' : SubDomainLeCoe (x ⊔ (y ⊓ z)) z := ⟨ϕ, lattice₁ p⟩
  (φ * ψ) ↓ z = ϕ'


lemma proof_2p1p3
    : Statement2p1p3 φ ψ h₁ h₂
    := by

  done
