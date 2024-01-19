import InformationAlgebra.Chapter2.P1Basic

/-!
# Marginalization

In this file we define the operation of marginalization, and provide some re-usable theorems.


## Implementation

Marginalization sucks. It's dependent type is what makes this whole enterprise difficult.
-/


namespace ValuationAlgebra


variable
  {D : Type*}
  (Φ : D → Type*)


class GMargin [LE D] where
  /-- Marginalization over sub-grades -/
  margin (φ : Φ x) (y : D) (p : y ≤ x) : Φ y


@[inherit_doc]
notation:10000 "(" φ " ⇓ " x ", " p ")" => GMargin.margin φ x p


-- For pretty printing
notation:70 φ " ↓ " x => (φ ⇓ x, _)


section MarginTrans


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


end MarginTrans
