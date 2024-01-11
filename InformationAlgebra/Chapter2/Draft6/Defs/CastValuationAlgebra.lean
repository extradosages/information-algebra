import InformationAlgebra.Chapter2.Draft6.Defs.Basic


open ValuationAlgebra


namespace CastValuationAlgebra


variable
  {D : Type*}
  {Φ : D → Type*}
  {x y z : D}
  (φ : Φ x)
  (ψ : Φ y)
  (ϕ : Φ z)


protected def StrongMulCommStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] (p : y ⊔ x = x ⊔ y) :=
  φ ⊗ ψ = p↾ (ψ ⊗ φ)


protected def WeakMulCommStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] :=
  CastValuationAlgebra.StrongMulCommStatement φ ψ sup_comm


protected def StrongMulAssocStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] (p : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z) :=
  (φ ⊗ ψ) ⊗ ϕ = p↾ (φ ⊗ (ψ ⊗ ϕ))


protected def WeakMulAssocStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] :=
  CastValuationAlgebra.StrongMulAssocStatement φ ψ ϕ sup_assoc.symm


protected def StrongMulOneStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] [GOne Φ] (p : x ⊔ x = x) :=
  φ = p↾ (φ ⊗ e x)


protected def WeakMulOneStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] [GOne Φ] :=
  CastValuationAlgebra.StrongMulOneStatement φ sup_idem


protected def StrongMarginMulStatement
    [Lattice D] [GCast Φ] [GMul Φ] [GOne Φ] [GMargin Φ] (p : x ≤ x ⊔ y) (q : x ⊓ y ≤ y) (r : x ⊔ x ⊓ y = x) :=
  (φ ⊗ ψ ⇓ x, p) = r↾ (φ ⊗ (ψ ⇓ x ⊓ y, q))


protected def WeakMarginMulStatement
    [DistribLattice D] [GCast Φ] [GMul Φ] [GOne Φ] [GMargin Φ] :=
  CastValuationAlgebra.StrongMarginMulStatement φ ψ le_sup_left inf_le_right sup_inf_self


class CastValuationAlgebra [DistribLattice D] extends GCastRefl Φ, GMul Φ, GOne Φ, GMarginRefl Φ where
  /-- Inter-grade multiplication is commutative -/
  mul_comm {x y : D} (φ : Φ x) (ψ : Φ y) (p : y ⊔ x = x ⊔ y) : CastValuationAlgebra.StrongMulCommStatement φ ψ p
  /-- Inter-grade multiplication is associative -/
  mul_assoc {x y z : D} (φ : Φ x) (ψ : Φ y) (ϕ : Φ z) (p : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z) : CastValuationAlgebra.StrongMulAssocStatement φ ψ ϕ p
  /-- Intra-grade multiplication by the grade's `one` is the identity -/
  mul_one {x y : D} (φ : Φ x) (p : x ⊔ x = x) : CastValuationAlgebra.StrongMulOneStatement φ p
  /-- Inter-grade multiplication of `one` elements produces a `one` element -/
  one_mul_one (x y : D) : ValuationAlgebra.OneMulOneStatement Φ x y
  /-- Marginalization respects transitivity of sub-grades -/
  margin_trans {x y z : D} (φ : Φ x) (p : z ≤ y) (q : y ≤ x) (r : z ≤ x) : ValuationAlgebra.StrongMarginTransStatement Φ φ p q r
  /-- Marginalization distributes across multiplication in a particular way -/
  margin_mul {x y : D} (φ : Φ x) (ψ : Φ y) (p : x ≤ x ⊔ y) (q : x ⊓ y ≤ y) (r : x ⊔ x ⊓ y = x) : CastValuationAlgebra.StrongMarginMulStatement φ ψ p q r


class WeakCastValuationAlgebra [DistribLattice D] extends GCastRefl Φ, GMul Φ, GOne Φ, GWeakMarginRefl Φ where
  /-- Inter-grade multiplication is commutative -/
  mul_comm {x y : D} (φ : Φ x) (ψ : Φ y) : CastValuationAlgebra.WeakMulCommStatement φ ψ
  /-- Inter-grade multiplication is associative -/
  mul_assoc {x y z : D} (φ : Φ x) (ψ : Φ y) (ϕ : Φ z) : CastValuationAlgebra.WeakMulAssocStatement φ ψ ϕ
  /-- Intra-grade multiplication by the grade's `one` is the identity -/
  mul_one {x y : D} (φ : Φ x) : CastValuationAlgebra.WeakMulOneStatement φ
  /-- Inter-grade multiplication of `one` elements produces a `one` element -/
  one_mul_one (x y : D) : ValuationAlgebra.OneMulOneStatement Φ x y
  /-- Marginalization respects transitivity of sub-grades -/
  margin_trans {x y z : D} (φ : Φ x) (p : z ≤ y) (q : y ≤ x) : ValuationAlgebra.WeakMarginTransStatement Φ φ p q
  /-- Marginalization distributes across multiplication in a particular way -/
  margin_mul {x y : D} (φ : Φ x) (ψ : Φ y) : CastValuationAlgebra.WeakMarginMulStatement φ ψ
