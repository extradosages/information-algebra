import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib


namespace ValuationAlgebra


variable
  {D : Type*}
  (Φ : D → Type*)


class GCast where
  /-- Cast terms of one grade to another when those grades can be equated -/
  cast : x = y → Φ x → Φ y


@[inherit_doc]
infixl:1000 "↾ " => GCast.cast


class GCastRefl extends GCast Φ where
  /-- Reflexivity casts to the identity -/
  cast_refl (φ : Φ x) : rfl↾ φ = φ


class GMul [SemilatticeSup D] where
  /-- Inter-grade multiplication -/
  mul : Φ x → Φ y → Φ (x ⊔ y)


@[inherit_doc]
infixl:70 (priority := high) " ⊗ " => GMul.mul


class GOne where
  /-- Each grade has a `one` -/
  one x : Φ x


@[inherit_doc]
notation:80 "e " x => GOne.one x


class GMargin [LE D] where
  /-- Marginalization over sub-grades -/
  margin (φ : Φ x) (y : D) (p : y ≤ x) : Φ y


@[inherit_doc]
notation:10000 "(" φ " ⇓ " x ", " p ")" => GMargin.margin φ x p


-- For pretty printing
notation:70 φ " ↓ " x => (φ ⇓ x, _)


-- TODO: Might be the case that this can produce a cast
protected def StrongMarginReflStatement
    [LE D] [GMargin Φ] (φ : Φ x) (p : x ≤ x) :=
  φ = (φ ⇓ x, p)


protected def WeakMarginReflStatement
    [Preorder D] [GMargin Φ] (φ : Φ x) :=
  ValuationAlgebra.StrongMarginReflStatement Φ φ (le_refl x)


class GMarginRefl [LE D] extends GMargin Φ where
  /-- Marginalization by a valuation's grade is the identity -/
  margin_refl (φ : Φ x) (p : x ≤ x) : ValuationAlgebra.StrongMarginReflStatement Φ φ p


class GWeakMarginRefl [Preorder D] extends GMargin Φ where
  /-- Marginalization by a valuation's grade is the identity -/
  margin_refl (φ : Φ x) : ValuationAlgebra.WeakMarginReflStatement Φ φ


protected def OneMulOneStatement
    [SemilatticeSup D] (Φ : D → Type*) [GMul Φ] [GOne Φ] (x y : D) :=
  (e x : Φ x) ⊗ (e y) = (e x ⊔ y)


protected def StrongMarginTransStatement
    [LE D] [GMargin Φ] {x y z : D} (φ : Φ x) (p : z ≤ y) (q : y ≤ x) (r : z ≤ x) :=
  (φ ⇓ z, r) = ((φ ⇓ y, q) ⇓ z, p)


protected def WeakMarginTransStatement
    [Preorder D] [GMargin Φ] {x y : D} (φ : Φ x) (p : z ≤ y) (q : y ≤ x) :=
  ValuationAlgebra.StrongMarginTransStatement Φ φ p q (le_trans p q)
