import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib


namespace ValuationAlgebra


variable
  {D : Type u}
  (Φ : D → Type v)


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


/-- The type of proofs homotopic to a basepoint (not quite; see definition).

Coerces to the type of the basepoint. Has usefult `default`: the basepoint.-/
structure HomotopicTo {Statement : Prop} (basepoint : Statement) where
  point : Statement
  -- NOTE: Right now I'm just leaving this out, so this isn't *really* a type for homotopic proofs
  -- homotopy : sorry


instance {Statement : Prop} {basepoint : Statement} : CoeOut (HomotopicTo basepoint) Statement where
  coe := fun ⟨point⟩ ↦ point


instance : Inhabited (HomotopicTo proof) where
  default := ⟨proof⟩


notation:70 "~" bp => HomotopicTo bp


/- NOT TRUE IN GENERAL
-- TODO: Might be the case that this can produce a cast
protected def StrongMarginReflStatement
    [Preorder D] [GMargin Φ] (φ : Φ x) (h_le_refl : HomotopicTo (le_refl x)) :=
  φ = (φ ⇓ x, h_le_refl)


protected def WeakMarginReflStatement
    [Preorder D] [GMargin Φ] (φ : Φ x) :=
  ValuationAlgebra.StrongMarginReflStatement Φ φ default


class GMarginRefl [Preorder D] extends GMargin Φ where
  /-- Marginalization by a valuation's grade is the identity -/
  margin_refl
    {x : D}
    (φ : Φ x)
    (h_le_refl : HomotopicTo (le_refl x))
    : ValuationAlgebra.StrongMarginReflStatement Φ φ h_le_refl


class GWeakMarginRefl [Preorder D] extends GMargin Φ where
  /-- Marginalization by a valuation's grade is the identity -/
  margin_refl {x : D} (φ : Φ x) : ValuationAlgebra.WeakMarginReflStatement Φ φ
-/

protected def OneMulOneStatement
    [SemilatticeSup D] (Φ : D → Type*) [GMul Φ] [GOne Φ] (x y : D) :=
  (e x : Φ x) ⊗ (e y) = (e x ⊔ y)


protected def StrongMarginTransStatement
    [Preorder D]
    [GMargin Φ]
    {x y z : D}
    (φ : Φ x)
    (h_le₁ : z ≤ y)
    (h_le₂ : y ≤ x)
    (h_le_trans : HomotopicTo (le_trans h_le₁ h_le₂))
    :=
  (φ ⇓ z, h_le_trans) = ((φ ⇓ y, h_le₂) ⇓ z, h_le₁)


protected def WeakMarginTransStatement
    [Preorder D] [GMargin Φ] {x y : D} (φ : Φ x) (h_le₁ : z ≤ y) (h_le₂ : y ≤ x) :=
  ValuationAlgebra.StrongMarginTransStatement Φ φ h_le₁ h_le₂ default
