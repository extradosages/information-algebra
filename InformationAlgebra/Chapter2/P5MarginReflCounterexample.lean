import InformationAlgebra.Chapter2.Draft6.Defs.CastValuationAlgebra

/-!
# Margin Refl Counterexample

This file attempts to demonstrate the counterexample to the generic assertion that marginalizing a
valuation by its domain is the identity.

JK:
> A word of warning: it may be conjectured that if `φ : Φ x`, then `(φ ⇓ x, _) = φ`. This is however
> not true in general. Consider for example a valuation algebra `Φ` and double each element, by
> distinguishing two versions of each element, one marked, one unmarked. Both behave the same way,
> except that the marginal of each element is marked, and when any valuation in a combination is
> marked, then so is the combination. This system is still a valuation algebra, but `(φ ⇓ x, _) ≠ x`,
> if `φ` is not marked (this example is due to (Shafer, 1991)).

## Implementation

The "marked/unmarked" construction is given by a type on the internal gradation that sends each
grade to a disjoint union of itself with a duplicate copy.

-/


open ValuationAlgebra
open CastValuationAlgebra
open Sum


namespace MarginReflCounterexample


variable
  {D : Type u}
  [DistribLattice D]
  {x y : D}
  (Φ : D → Type v)
  [CastValuationAlgebra Φ]


/-- The "marked/unmarked" construction. -/
def Duplicate (x : D) : Type v := (Φ x) ⊕ (Φ x)


/-- The pathological marginalization instance. -/
local instance : GMargin (Duplicate Φ) where
  margin φφ y p := match φφ with
    | inl φ => inl (φ ⇓ y, p)
    | inr φ => inl (φ ⇓ y, p)


/-- The pathological marginalization instance has an element which is not reflexively
marginalizable. -/
theorem not_margin_refl (φ : Φ x) : @GMargin.margin _ (Duplicate Φ) _ _ _ (inr φ) x (le_refl x) ≠ inr φ := by
  dsimp only [GMargin.margin]
  simp_all only [ne_eq, not_false_eq_true]
  done


/-
At this point, we've demonstrated almost all of what JK says-- except for the assertion that
the duplicated construction is "still a valuation system."

Below, we attempt to validate that statement by continuing to construct a `CastValuationAlgebra`
instance.

TODO: This is not straightforward...
-/


local instance : GOne (Duplicate Φ) where
  one x := inl (e x)


local instance : GCastRefl (Duplicate Φ) where
  cast p φφ := match φφ with
    | inl φ => inl (GCast.cast p φ)
    | inr φ => inr (GCast.cast p φ)
  cast_refl φφ := by
    cases φφ <;> (dsimp; congr; apply GCastRefl.cast_refl)
    done


local instance : GMul (Duplicate Φ) where
  mul φφ ψψ := match (φφ, ψψ) with
    | (inl φ, inl ψ) => inl (φ ⊗ ψ)
    | (inl φ, inr ψ) => inl (φ ⊗ ψ)
    | (inr φ, inl ψ) => inl (φ ⊗ ψ)
    | (inr φ, inr ψ) => inl (φ ⊗ ψ)
