import InformationAlgebra.Chapter2.Draft6.Defs.Basic


open ValuationAlgebra


namespace CastValuationAlgebra


section classes


variable
  {D : Type u}
  {Φ : D → Type v}
  {x y z : D}
  (φ : Φ x)
  (ψ : Φ y)
  (ϕ : Φ z)


protected def StrongMulCommStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] (h_sup_comm : HomotopicTo (sup_comm : y ⊔ x = x ⊔ y)) :=
  φ ⊗ ψ = h_sup_comm↾ (ψ ⊗ φ)


protected def WeakMulCommStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] :=
  CastValuationAlgebra.StrongMulCommStatement φ ψ default


protected def StrongMulAssocStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] (h_sup_assoc : HomotopicTo (sup_assoc.symm : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z)) :=
  (φ ⊗ ψ) ⊗ ϕ = h_sup_assoc↾ (φ ⊗ (ψ ⊗ ϕ))


protected def WeakMulAssocStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] :=
  CastValuationAlgebra.StrongMulAssocStatement φ ψ ϕ default


protected def StrongMulOneStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] [GOne Φ] (h_sup_idem : HomotopicTo (sup_idem : x ⊔ x = x)) :=
  φ = h_sup_idem↾ (φ ⊗ e x)


protected def WeakMulOneStatement
    [GCast Φ] [SemilatticeSup D] [GMul Φ] [GOne Φ] :=
  CastValuationAlgebra.StrongMulOneStatement φ default


protected def StrongMarginMulStatement
    [Lattice D]
    [GCast Φ]
    [GMul Φ]
    [GOne Φ]
    [GMargin Φ]
    (h_le_sup_left : HomotopicTo (le_sup_left :x ≤ x ⊔ y))
    (h_inf_le_right : HomotopicTo (inf_le_right : x ⊓ y ≤ y))
    (h_sup_inf_self : HomotopicTo (sup_inf_self : x ⊔ x ⊓ y = x))
    :=
  (φ ⊗ ψ ⇓ x, h_le_sup_left) = h_sup_inf_self↾ (φ ⊗ (ψ ⇓ x ⊓ y, h_inf_le_right))


protected def WeakMarginMulStatement
    [DistribLattice D] [GCast Φ] [GMul Φ] [GOne Φ] [GMargin Φ] :=
  CastValuationAlgebra.StrongMarginMulStatement φ ψ default default default


-- Strong version of the structure in which every proof of equality and order is generalized
-- to the class of proofs which are "homotopic" with the "default" ones
class StrongCastValuationAlgebra [DistribLattice D] (Φ : D → Type*) extends GCastRefl Φ, GMul Φ, GOne Φ, GMargin Φ where
  /-- Inter-grade multiplication is commutative -/
  mul_comm
    {x y : D}
    (φ : Φ x)
    (ψ : Φ y)
    (h_sup_comm : HomotopicTo (sup_comm : y ⊔ x = x ⊔ y))
    : CastValuationAlgebra.StrongMulCommStatement φ ψ h_sup_comm
  /-- Inter-grade multiplication is associative -/
  mul_assoc
    {x y z : D}
    (φ : Φ x)
    (ψ : Φ y)
    (ϕ : Φ z)
    (h_sup_assoc : HomotopicTo (sup_assoc.symm : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z))
    : CastValuationAlgebra.StrongMulAssocStatement φ ψ ϕ h_sup_assoc
  /-- Intra-grade multiplication by the grade's `one` is the identity -/
  mul_one
    {x : D}
    (φ : Φ x)
    (h_sup_idem : HomotopicTo (sup_idem : x ⊔ x = x))
    : CastValuationAlgebra.StrongMulOneStatement φ h_sup_idem
  /-- Inter-grade multiplication of `one` elements produces a `one` element -/
  one_mul_one (x y : D) : ValuationAlgebra.OneMulOneStatement Φ x y
  /-- Marginalization respects transitivity of sub-grades -/
  margin_trans
    {x y z : D}
    (φ : Φ x)
    (h_le₁ : z ≤ y)
    (h_le₂ : y ≤ x)
    (h_le_trans : HomotopicTo (le_trans h_le₁ h_le₂))
    : ValuationAlgebra.StrongMarginTransStatement Φ φ h_le₁ h_le₂ h_le_trans
  /-- Marginalization distributes across multiplication in a particular way -/
  margin_mul
    {x y : D}
    (φ : Φ x)
    (ψ : Φ y)
    (h_le_sup_left : HomotopicTo (le_sup_left : x ≤ x ⊔ y))
    (h_inf_le_right : HomotopicTo (inf_le_right : x ⊓ y ≤ y))
    (h_sup_inf_self : HomotopicTo (sup_inf_self : x ⊔ x ⊓ y = x))
    : CastValuationAlgebra.StrongMarginMulStatement φ ψ h_le_sup_left h_inf_le_right h_sup_inf_self


class CastValuationAlgebra [DistribLattice D] (Φ : D → Type*) extends GCastRefl Φ, GMul Φ, GOne Φ, GMargin Φ where
  /-- Inter-grade multiplication is commutative -/
  mul_comm {x y : D} (φ : Φ x) (ψ : Φ y) : CastValuationAlgebra.WeakMulCommStatement φ ψ
  /-- Inter-grade multiplication is associative -/
  mul_assoc {x y z : D} (φ : Φ x) (ψ : Φ y) (ϕ : Φ z) : CastValuationAlgebra.WeakMulAssocStatement φ ψ ϕ
  /-- Intra-grade multiplication by the grade's `one` is the identity -/
  mul_one {x : D} (φ : Φ x) : CastValuationAlgebra.WeakMulOneStatement φ
  /-- Inter-grade multiplication of `one` elements produces a `one` element -/
  one_mul_one (x y : D) : ValuationAlgebra.OneMulOneStatement Φ x y
  /-- Marginalization respects transitivity of sub-grades -/
  margin_trans {x y z : D} (φ : Φ x) (h_le₁ : z ≤ y) (h_le₂ : y ≤ x) : ValuationAlgebra.WeakMarginTransStatement Φ φ h_le₁ h_le₂
  /-- Marginalization distributes across multiplication in a particular way -/
  margin_mul {x y : D} (φ : Φ x) (ψ : Φ y) : CastValuationAlgebra.WeakMarginMulStatement φ ψ


end classes


section theorems


open GCastRefl
open CastValuationAlgebra


variable
  [DistribLattice D]
  {Φ : D → Type*}
  {x y z : D}


@[simp]
theorem cast_symm [GCastRefl Φ] {φ : Φ x} {ψ : Φ y} : (p↾ φ) = ψ ↔ φ = (p.symm↾ ψ) := by
  cases p
  rw [cast_refl, cast_refl]
  done


@[simp]
theorem cast_symm_cast_left [GCastRefl Φ] {φ : Φ x} {ψ : Φ y} (q : (p↾ φ) = ψ) : φ = (p.symm↾ ψ) :=
  cast_symm.mp q


@[simp]
theorem cast_symm_cast_right [GCastRefl Φ] {φ : Φ x} {ψ : Φ y} (q : φ = (p↾ ψ)) : (p.symm↾ φ) = ψ :=
  cast_symm.mpr q


/-- Casting across two equalities is casting across their transitivity -/
theorem cast_trans [GCastRefl Φ] {φ : Φ x} {p : x = y} {q : y = z} : q↾ (p↾ φ) = (p.trans q)↾ φ := by
  cases p
  cases q
  rw [cast_refl, cast_refl]
  done


@[simp]
theorem cast_mul_left [GCastRefl Φ] [GMul Φ] {φ : Φ x} {ψ : Φ y} {p : x = z} : (p↾ φ) ⊗ ψ = (congrArg (· ⊔ y) p)↾ (φ ⊗ ψ) := by
  cases p
  rw [cast_refl, cast_refl]
  done


@[simp]
theorem cast_mul_right [GCastRefl Φ] [GMul Φ] {φ : Φ x} {ψ : Φ y} {p : y = z} : φ ⊗ (p↾ ψ) = (congrArg (x ⊔ ·) p)↾ (φ ⊗ ψ) := by
  cases p
  rw [cast_refl, cast_refl]
  done


@[simp]
theorem cast_margin_le_of_eq [GCastRefl Φ] [GMargin Φ] {φ : Φ x} {q : x = z} : (φ ⇓ y, p) = ((q↾ φ) ⇓ y, le_of_le_of_eq p q) := by
  cases q
  rw [cast_refl]
  done


@[simp]
theorem cast_margin_eq_of_le [GCastRefl Φ] [GMargin Φ] {φ : Φ x} (q : z = y) : (φ ⇓ y, p) = q↾ (φ ⇓ z, le_of_eq_of_le q p) := by
  cases q
  rw [cast_refl]
  done


@[simp]
theorem strong_mul_assoc_cast_right
    [StrongCastValuationAlgebra Φ]
    {φ : Φ x}
    {ψ : Φ y}
    {ϕ : Φ z}
    (h_sup_assoc : HomotopicTo (sup_assoc.symm : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z))
    :
    ((φ ⊗ ψ) ⊗ ϕ) = h_sup_assoc↾ (φ ⊗ (ψ ⊗ ϕ))
    :=
  StrongCastValuationAlgebra.mul_assoc φ ψ ϕ h_sup_assoc


@[simp]
theorem mul_assoc_cast_right
    [CastValuationAlgebra Φ]
    {φ : Φ x}
    {ψ : Φ y}
    {ϕ : Φ z}
    :
    ((φ ⊗ ψ) ⊗ ϕ) = sup_assoc.symm↾ (φ ⊗ (ψ ⊗ ϕ))
    :=
  mul_assoc φ ψ ϕ


@[simp]
theorem strong_mul_assoc_cast_left
    [StrongCastValuationAlgebra Φ]
    {φ : Φ x}
    {ψ : Φ y}
    {ϕ : Φ z}
    (h_sup_assoc : HomotopicTo (sup_assoc : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)))
    :
    h_sup_assoc↾ ((φ ⊗ ψ) ⊗ ϕ) = (φ ⊗ (ψ ⊗ ϕ))
    :=
  cast_symm_cast_right <| StrongCastValuationAlgebra.mul_assoc φ ψ ϕ ⟨Eq.symm h_sup_assoc⟩


@[simp]
theorem mul_assoc_cast_left
    [CastValuationAlgebra Φ]
    {φ : Φ x}
    {ψ : Φ y}
    {ϕ : Φ z}
    :
    sup_assoc↾ ((φ ⊗ ψ) ⊗ ϕ) = (φ ⊗ (ψ ⊗ ϕ))
    :=
  cast_symm_cast_right <| mul_assoc φ ψ ϕ


@[simp]
theorem strong_mul_one_cast_right
    [StrongCastValuationAlgebra Φ]
    {φ : Φ x}
    (h_sup_idem : HomotopicTo (sup_idem : x ⊔ x = x))
    :
    φ = h_sup_idem↾ (φ ⊗ e x)
    :=
  StrongCastValuationAlgebra.mul_one φ h_sup_idem


@[simp]
theorem mul_one_cast_right
    [CastValuationAlgebra Φ]
    {φ : Φ x}
    :
    φ = sup_idem↾ (φ ⊗ e x)
    :=
  mul_one φ


@[simp]
theorem strong_mul_one_cast_left
    [StrongCastValuationAlgebra Φ]
    {φ : Φ x}
    (h_sup_idem : HomotopicTo (sup_idem.symm : x = x ⊔ x))
    :
    h_sup_idem↾ φ = φ ⊗ e x
    :=
  cast_symm_cast_right <| StrongCastValuationAlgebra.mul_one φ ⟨Eq.symm h_sup_idem⟩


@[simp]
theorem mul_one_cast_left
    [CastValuationAlgebra Φ]
    {φ : Φ x}
    :
    sup_idem.symm↾ φ = φ ⊗ e x
    :=
  cast_symm_cast_right <| mul_one φ


@[simp]
theorem strong_margin_mul_cast_right
    [StrongCastValuationAlgebra Φ]
    {φ : Φ x}
    {ψ : Φ y}
    (h_le_sup_left : HomotopicTo (le_sup_left : x ≤ x ⊔ y))
    (h_inf_le_right : HomotopicTo (inf_le_right : x ⊓ y ≤ y))
    (h_sup_inf_self : HomotopicTo (sup_inf_self : x ⊔ x ⊓ y = x))
    :
    (φ ⊗ ψ ⇓ x, h_le_sup_left) = h_sup_inf_self↾ (φ ⊗ (ψ ⇓ x ⊓ y, h_inf_le_right))
    :=
  StrongCastValuationAlgebra.margin_mul φ ψ h_le_sup_left h_inf_le_right h_sup_inf_self


@[simp]
theorem margin_mul_cast_right
    [CastValuationAlgebra Φ]
    {φ : Φ x}
    {ψ : Φ y}
    :
    (φ ⊗ ψ ⇓ x, le_sup_left) = sup_inf_self↾ (φ ⊗ (ψ ⇓ x ⊓ y, inf_le_right))
    :=
  margin_mul φ ψ


@[simp]
theorem strong_margin_mul_cast_left
    [StrongCastValuationAlgebra Φ]
    {φ : Φ x}
    {ψ : Φ y}
    (h_le_sup_left : HomotopicTo (le_sup_left : x ≤ x ⊔ y))
    (h_inf_le_right : HomotopicTo (inf_le_right : x ⊓ y ≤ y))
    (h_sup_inf_self : HomotopicTo (sup_inf_self.symm : x = x ⊔ x ⊓ y))
    :
    h_sup_inf_self↾ (φ ⊗ ψ ⇓ x, h_le_sup_left) = φ ⊗ (ψ ⇓ x ⊓ y, h_inf_le_right)
    :=
  cast_symm_cast_right <| StrongCastValuationAlgebra.margin_mul φ ψ h_le_sup_left h_inf_le_right ⟨Eq.symm h_sup_inf_self⟩


@[simp]
theorem margin_mul_cast_left
    [CastValuationAlgebra Φ]
    {φ : Φ x}
    {ψ : Φ y}
    :
    sup_inf_self.symm↾ (φ ⊗ ψ ⇓ x, le_sup_left) = φ ⊗ (ψ ⇓ x ⊓ y, inf_le_right)
    :=
  cast_symm_cast_right <| margin_mul φ ψ


end theorems
