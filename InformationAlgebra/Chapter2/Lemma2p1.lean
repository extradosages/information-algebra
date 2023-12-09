import InformationAlgebra.Chapter2.ValuationAlgebras


open ValuationAlgebras


section


variable
  (Φ s : Type)
  [instCommSemigroup : CommSemigroup Φ]
  [instValuationAlgebra : @ValuationAlgebra Φ s instCommSemigroup]
  (φ ψ ϕ : Φ)
  (x y z : Set s)


local infix:70 " ⊗ " => (· * ·)
local notation:10000 "ð" => instValuationAlgebra.domain
local infixl:1000 " ↓ " => Marginalize.marginalize


#check ValuationAlgebra.mul_marginalize φ ψ (x ∩ y) y


lemma dist_marginalization_combination
    (hφ : ð φ = x)
    (hψ : ð ψ = y)
    : (φ ⊗ ψ) ↓ (x ∩ y) = (φ ↓ (x ∩ y)) ⊗ (ψ ↓ (x ∩ y))
    := by
  have hx : x ∩ y ⊆ x := Set.inter_subset_left x y
  conv =>
    lhs
    rw [ValuationAlgebra.marginalize_trans (φ ⊗ ψ) (x ∩ y) x hx]
    rw [ValuationAlgebra.mul_marginalize φ ψ x y ⟨hφ, hψ⟩]
    rw [CommSemigroup.mul_comm]
  let ψ' := ψ ↓ (x ∩ y)
  have hψ' : ð ψ' = (x ∩ y) := by
    apply ValuationAlgebra.domain_marginalize
  conv =>
    lhs
    rw [ValuationAlgebra.mul_marginalize ψ' φ (x ∩ y) x ⟨hψ', hφ⟩]
  conv =>
    lhs
    rhs
    rw [Set.inter_comm, ← Set.inter_assoc, Set.inter_self x]
  apply CommSemigroup.mul_comm


lemma dist_subset_marginalization_combination
    (hφ : ð φ = x)
    (hψ : ð ψ = y)
    (hz : z ⊆ x)
    : (φ ⊗ ψ) ↓ z = (φ ⊗ (ψ ↓ (x ∩ y))) ↓ z
    := by

  sorry


lemma dist_superset_marginalization_combination
  (hφ : ð φ = x)
  (hψ : ð ψ = y)
  (hz₁ : x ⊆ z)
  (hz₂ : z ⊆ x ∪ y)
  : (φ ⊗ ψ) ↓ z = φ ⊗ (ψ ↓ (y ∩ z))
  := by
    sorry

end
