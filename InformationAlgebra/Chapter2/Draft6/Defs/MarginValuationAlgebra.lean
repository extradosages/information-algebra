import InformationAlgebra.Chapter2.Draft6.Defs.Basic


open ValuationAlgebra


namespace MarginValuationAlgebra


variable
  {D : Type*}
  {Φ : D → Type*}
  {x y z : D}
  (φ : Φ x)
  (ψ : Φ y)
  (ϕ : Φ z)


protected def StrongMulCommStatement
    [SemilatticeSup D] [GMargin Φ] [GMul Φ] (p : x ⊔ y ≤ y ⊔ x) :=
  φ ⊗ ψ = (ψ ⊗ φ ⇓ x ⊔ y, p)


protected def WeakMulCommStatement
    [SemilatticeSup D] [GMargin Φ] [GMul Φ] :=
  MarginValuationAlgebra.StrongMulCommStatement φ ψ (le_of_eq sup_comm)


protected def StrongMulAssocStatement
    [SemilatticeSup D] [GMargin Φ] [GMul Φ] (p : (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)) :=
  (φ ⊗ ψ) ⊗ ϕ = (φ ⊗ (ψ ⊗ ϕ) ⇓ (x ⊔ y) ⊔ z, p)


protected def WeakMulAssocStatement
    [SemilatticeSup D] [GMargin Φ] [GMul Φ] :=
  MarginValuationAlgebra.StrongMulAssocStatement φ ψ ϕ (le_of_eq sup_assoc)


protected def StrongMulOneStatement
    [SemilatticeSup D] [GMargin Φ] [GMul Φ] [GOne Φ] (p : x ≤ x ⊔ x) :=
  φ = ((φ ⊗ e x) ⇓ x, p)


protected def WeakMulOneStatement
    [SemilatticeSup D] [GMargin Φ] [GMul Φ] [GOne Φ] :=
  MarginValuationAlgebra.StrongMulOneStatement φ le_sup_left



protected def StrongMarginMulStatement
    [Lattice D] [GMargin Φ] [GMul Φ] [GOne Φ] (p : x ≤ x ⊔ y) (q : x ⊓ y ≤ y) (r : x ≤ x ⊔ x ⊓ y) :=
  (φ ⊗ ψ ⇓ x, p) = ((φ ⊗ (ψ ⇓ x ⊓ y, q)) ⇓ x, r)


protected def WeakMarginMulStatement
    [DistribLattice D] [GMargin Φ] [GMul Φ] [GOne Φ] :=
  MarginValuationAlgebra.StrongMarginMulStatement φ ψ le_sup_left inf_le_right le_sup_left


class CastValuationAlgebra [DistribLattice D] extends GMul Φ, GOne Φ, GMarginRefl Φ where
  /-- Inter-grade multiplication is commutative -/
  mul_comm {x y : D} (φ : Φ x) (ψ : Φ y) (p : x ⊔ y ≤ y ⊔ x) : MarginValuationAlgebra.StrongMulCommStatement φ ψ p
  /-- Inter-grade multiplication is associative -/
  mul_assoc {x y z : D} (φ : Φ x) (ψ : Φ y) (ϕ : Φ z) (p : (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)) : MarginValuationAlgebra.StrongMulAssocStatement φ ψ ϕ p
  /-- Intra-grade multiplication by the grade's `one` is the identity -/
  mul_one {x y : D} (φ : Φ x) (p : x ≤ x ⊔ x) : MarginValuationAlgebra.StrongMulOneStatement φ p
  /-- Inter-grade multiplication of `one` elements produces a `one` element -/
  one_mul_one (x y : D) : ValuationAlgebra.OneMulOneStatement Φ x y
  /-- Marginalization respects transitivity of sub-grades -/
  margin_trans {x y z : D} (φ : Φ x) (p : z ≤ y) (q : y ≤ x) (r : z ≤ x) : ValuationAlgebra.StrongMarginTransStatement Φ φ p q r
  /-- Marginalization distributes across multiplication in a particular way -/
  margin_mul {x y : D} (φ : Φ x) (ψ : Φ y) (p : x ≤ x ⊔ y) (q : x ⊓ y ≤ y) (r : x ≤ x ⊔ x ⊓ y) : MarginValuationAlgebra.StrongMarginMulStatement φ ψ p q r


class WeakCastValuationAlgebra [DistribLattice D] extends GMul Φ, GOne Φ, GMarginRefl Φ where
  /-- Inter-grade multiplication is commutative -/
  mul_comm {x y : D} (φ : Φ x) (ψ : Φ y) : MarginValuationAlgebra.WeakMulCommStatement φ ψ
  /-- Inter-grade multiplication is associative -/
  mul_assoc {x y z : D} (φ : Φ x) (ψ : Φ y) (ϕ : Φ z) : MarginValuationAlgebra.WeakMulAssocStatement φ ψ ϕ
  /-- Intra-grade multiplication by the grade's `one` is the identity -/
  mul_one {x y : D} (φ : Φ x) : MarginValuationAlgebra.WeakMulOneStatement φ
  /-- Inter-grade multiplication of `one` elements produces a `one` element -/
  one_mul_one (x y : D) : ValuationAlgebra.OneMulOneStatement Φ x y
  /-- Marginalization respects transitivity of sub-grades -/
  margin_trans {x y z : D} (φ : Φ x) (p : z ≤ y) (q : y ≤ x) : ValuationAlgebra.WeakMarginTransStatement Φ φ p q
  /-- Marginalization distributes across multiplication in a particular way -/
  margin_mul {x y : D} (φ : Φ x) (ψ : Φ y) : MarginValuationAlgebra.WeakMarginMulStatement φ ψ
