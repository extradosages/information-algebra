import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib

/-!
# Basic definitions for valuation systems

Here we define basic typeclasses for operations in *abstract* valuation systems.

## Implementation

*Abstract* valuation systems are implemented with an abstract "internal gradation", that is, a
dependent type from a grade "value" to the elements of the system attached to the grade.

From [a discussion on zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Identities.20to.20Equivalences.20in.20Graded.20Structures/near/410059564) about how to implement graded structures like this:
> For those following and interested, I'll give a brief description of what Wieser and Zhang write.
>
> First, they highlight the point that @**Trebor Huang** made, that there's an equivalence between "internally" and "externally" graded types: internal gradation is a map from a large type to the grade; and external gradation is a dependent type from the grade. They use externally graded types for discussion.
>
> Using the construction of a graded semi-group as an example, they present 6 options for pushing an identity in the domain of an externally graded type to equivalence between components (quoting directly from the paper):
>
> 1. Use heterogenous equality (denoted `==`), which allows us to express equality
> between distinct types ([ex](https://github.com/eric-wieser/lean-graded-rings/blob/cf463b1b9317e16499a51b20037ad8319311bd21/src/cicm2022/examples/graded_semigroup.lean#L16?decl=heq.g_semigroup).
> 2. Express the equality in terms of sigma types or dependent pairs, denoted
> `Σ i, A i` ([ex](https://github.com/eric-wieser/lean-graded-rings/blob/cf463b1b9317e16499a51b20037ad8319311bd21/src/cicm2022/examples/graded_semigroup.lean#L21?decl=sigma.g_semigroup)).
> 3. Express the grading constraint as an equality on sigma types ([ex](https://github.com/eric-wieser/lean-graded-rings/blob/cf463b1b9317e16499a51b20037ad8319311bd21/src/cicm2022/examples/graded_semigroup.lean#L26?decl=extends.g_semigroup)).
> 4. Provide an explicit proof that the equality is type correct using the recursor
> for equality, `eq.rec` ([ex](https://github.com/eric-wieser/lean-graded-rings/blob/cf463b1b9317e16499a51b20037ad8319311bd21/src/cicm2022/examples/graded_semigroup.lean#L30?decl=eq.rec.g_semigroup)).
> 5. Store a canonical map between objects of the “same” grade to use instead
> of using `eq.rec`, to allow better definitional control ([ex](https://github.com/eric-wieser/lean-graded-rings/blob/cf463b1b9317e16499a51b20037ad8319311bd21/src/cicm2022/examples/graded_semigroup.lean#L35?decl=cast.g_semigroup)).
> 6. Take an additional index into `mul` (they're talking about a graded semigroup) and a proof that it is equal to `i + j` ([ex](https://github.com/eric-wieser/lean-graded-rings/blob/cf463b1b9317e16499a51b20037ad8319311bd21/src/cicm2022/examples/graded_semigroup.lean#L42?decl=h%20:%20i+j=k.g_semigroup)).
-/


namespace ValuationAlgebra


variable
  {D : Type u}
  (Φ : D → Type v)


/-- A typeclass in which graded terms can be cast to one another.

Used essentially to provide notation for the definition of the more useful class `GCastRefl`.
You should probably always be using `GCastRefl`.-/
class GCast where
  /-- Cast terms of one grade to another when those grades can be equated -/
  cast : x = y → Φ x → Φ y


@[inherit_doc]
infixl:1000 "↾ " => GCast.cast


/-- A typeclass in which graded terms can be cast to one another. -/
class GCastRefl extends GCast Φ where
  /-- Reflexivity casts to the identity -/
  cast_refl (φ : Φ x) : rfl↾ φ = φ


/-- A typeclass in which graded terms can be multiplied. -/
class GMul [SemilatticeSup D] where
  /-- Inter-grade multiplication -/
  mul : Φ x → Φ y → Φ (x ⊔ y)


@[inherit_doc]
infixl:70 (priority := high) " ⊗ " => GMul.mul


/-- A typeclass in which each grade has a distinguished element. -/
class GOne where
  /-- Each grade has a `one` -/
  one x : Φ x


@[inherit_doc]
notation:80 "e " x => GOne.one x


protected def OneMulOneStatement
    [SemilatticeSup D] (Φ : D → Type*) [GMul Φ] [GOne Φ] (x y : D) :=
  (e x : Φ x) ⊗ (e y) = (e x ⊔ y)


section HomotopicTo
/-
This is a small collection of types that I was using to provide defaults to generalized proof
arguments in some janky dependent type theory places to help with debugging the construction
of proofs.

The principal structure is cheekily called `HomotopicTo` but it's not really the type of proofs
homotopic to a basepoint; that was too restrictive for my debugging purposes. But the name was
a helpful mnemonic.
-/


/-- The type of proofs homotopic to a basepoint (not quite; see definition).

Coerces to the type of the basepoint. Has usefult `default`: the basepoint.-/
structure HomotopicTo {Statement : Prop} (basepoint : Statement) where
  point : Statement
  /-
  NOTE: Right now I'm just leaving this out, so this isn't *really* a type for proofs homotopic
  to a basepoint.
  -/
  -- homotopy : sorry


instance {Statement : Prop} {basepoint : Statement} : CoeOut (HomotopicTo basepoint) Statement where
  coe := fun ⟨point⟩ ↦ point


instance : Inhabited (HomotopicTo proof) where
  default := ⟨proof⟩


notation:70 "~" bp => HomotopicTo bp


end HomotopicTo
