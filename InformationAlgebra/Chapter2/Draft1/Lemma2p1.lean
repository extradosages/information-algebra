import InformationAlgebra.Chapter2.Draft1.ValuationAlgebras


open ValuationAlgebras1


variable
  {Φ s : Type}
  [instCommSemigroup : CommSemigroup Φ]
  [instValuationAlgebra : @ValuationAlgebra Φ s instCommSemigroup]
  (φ ψ ϕ : Φ)


section


local notation:10000 "x" => (ð φ : Set s)
local notation:10000 "y" => (ð ψ : Set s)
local notation:10000 "xiy" => x ∩ y
local notation:10000 "xuy" => x ∪ y


private lemma hd₁
    : x ⊆ ð (φ ⊗ ψ) := by
  rw [DomainMulUnion.domain_mul_union]
  exact Set.subset_union_left x y
  done


private lemma hd₂
    : xiy ⊆ x
    := Set.inter_subset_left x y


private lemma hd₃
    : xiy ⊆ y
    := Set.inter_subset_right x y


private lemma hd₄
    : xiy ⊆ ð (φ ⊗ ψ) := by
  apply subset_trans
  apply hd₂
  apply hd₁
  done


lemma dist_marginalization_combination
    : (φ ⊗ ψ ↓ xiy, hd₄ φ ψ) = (φ ↓ xiy, hd₂ φ ψ) ⊗ (ψ ↓ xiy, hd₃ φ ψ)
    := by
  rw [ValuationAlgebra.marginalize_trans (hd₁ φ ψ) (hd₂ φ ψ)]
  conv =>
    pattern (occs := 2) (_ ↓ _, _)
    rw [ValuationAlgebra.mul_marginalize φ ψ]
    rw [CommSemigroup.mul_comm]
  conv =>
    lhs
    lhs
    rw [← DomainMarginalize.domain_marginalize (hd₃ φ ψ)]
  conv =>
    lhs
    rw [ValuationAlgebra.mul_marginalize (ψ ↓ xiy, hd₃ φ ψ) φ]
    rw [CommSemigroup.mul_comm]
    lhs
    pattern (occs := 1) ð (_ ↓ _, _)
    rw [DomainMarginalize.domain_marginalize (hd₃ φ ψ)]
  conv =>
    pattern (_ ∩ _ ∩ _)
    rw [Set.inter_comm, ← Set.inter_assoc, Set.inter_self]
  done


private lemma hd₅
    (hz : z ⊆ x)
    : z ⊆ ð (φ ⊗ ψ)
    := subset_trans hz (hd₁ φ ψ)


private lemma hd₆
    (hz : z ⊆ x)
    : z ⊆ ð (φ ⊗ (ψ ↓ xiy, hd₃ φ ψ))
    := by
  rw [DomainMulUnion.domain_mul_union]
  apply Set.subset_union_of_subset_left
  exact hz
  done


lemma dist_subset_marginalization_combination
    (hz : z ⊆ x)
    : ((φ ⊗ ψ) ↓ z, hd₅ φ ψ hz) = ((φ ⊗ (ψ ↓ xiy, hd₃ φ ψ)) ↓ z, hd₆ φ ψ hz)
    := by
  rw [ValuationAlgebra.marginalize_trans (hd₁ φ ψ)]
  conv =>
    pattern (_ ↓ ð _, _)
    rw [ValuationAlgebra.mul_marginalize φ ψ]
  exact hz
  done


private lemma hd₇
    (hz : z ⊆ xuy)
    : z ⊆ ð (φ ⊗ ψ)
    := by
  rw [DomainMulUnion.domain_mul_union]
  exact hz
  done


private lemma hd₈
    : y ∩ z ⊆ y
    := by
  exact Set.inter_subset_left y z
  done


lemma dist_superset_marginalization_combination
    (hz₁ : x ⊆ z)
    (hz₂ : z ⊆ xuy)
    : (φ ⊗ ψ ↓ z, hd₇ φ ψ hz₂) = φ ⊗ (ψ ↓ y ∩ z, hd₈ ψ)
    := by
  conv =>
    lhs
    pattern (_ ⊗ _ ↓ _, _)
    rw [← DomainPreimageMulOne.mul_one z (φ ⊗ ψ ↓ z, hd₇ φ ψ hz₂)]
  done

end
