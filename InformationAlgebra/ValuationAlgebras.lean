import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Subsemigroup.Basic
import Mathlib.Tactic.LibrarySearch

/-
TODO: Look up module docstring conventions
TODO: Add a namespace
TODO: Converge on good JK alias naming conventions (ex: `_jk`)
TODO: Fix naming conventions
TODO: Examine necessity and utility of the general typeclassing pattern here
-/

variable {α β : Type} (Φ : Type) (s : Type) (r : Set s) [Semigroup Φ]


-- Combining valuations
local infix:70 "⊗" => (. * .)


-- Getting a valuation's domain
class Domain where
  domain : Φ → Set s


--  Marginalizing a valuation
class Marginalize where
  marginalize: Φ → Set s → Φ


local infixl:70 "↓" => Marginalize.marginalize


-- Combining valuations
private class DomainMulUnion extends Domain Φ s where
  -- TODO: Not in love with this leading underscore; I'd like to keep those to aliases for
  -- terms that align with what JK uses in his book
  _mul_union : ∀ φ ψ : Φ, domain (φ * ψ) =  domain φ ∪ domain ψ


-- Preimages of domains
def DomainPreimage [Domain Φ s] := { x : Φ // Domain.domain x = r }


-- Surprised that there isn't a generic coercion from a subtype to the og type...
-- TODO: Using `CoeOut` here because `(DomainPreimage Φ s r)` is not concrete and `Coe` requires
-- that that argument be concrete; this was an uninformed choice, am I doing something wrong?
instance [Domain Φ s] : CoeOut (DomainPreimage Φ s r) Φ where
  coe φ := φ.val


/-
The preimage of any "mul union" domain is closed under multiplication.
-/
lemma preimage_domain_mul_closed
    [inst : DomainMulUnion Φ s]
    (φ : DomainPreimage Φ s r)
    (ψ : DomainPreimage Φ s r)
    :  Domain.domain ((φ : Φ) * ψ) = r
    := by
  have hφ : Domain.domain φ.val = r := φ.property
  have hψ : Domain.domain ψ.val = r := ψ.property
  let h := inst._mul_union φ.val ψ.val
  rw [h, hφ, hψ]
  exact Set.union_self r
  done


-- This _should_ make syntax easier...
instance [DomainMulUnion Φ s] : Mul (DomainPreimage Φ s r) where
  mul φ ψ := ⟨(φ : Φ) * ψ, preimage_domain_mul_closed Φ s r φ ψ⟩


-- TODO: This is probably superfluous
instance [DomainMulUnion Φ s] : Semigroup (DomainPreimage Φ s r) where
  mul_assoc := by
    intros φ ψ ϕ
    apply Subtype.ext_iff_val.mpr
    apply Semigroup.mul_assoc


private def domain_preimage_mul_left_one [DomainMulUnion Φ s] (e : DomainPreimage Φ s r) :=
  ∀ φ : DomainPreimage Φ s r,
    e * φ = φ


private def DomainPreimageMulRightOne [DomainMulUnion Φ s] (e : DomainPreimage Φ s r) :=
  ∀ φ : DomainPreimage Φ s r,
    φ * e = φ


-- TODO: This could have a better name
private def DomainPreimageMulOne' [DomainMulUnion Φ s] (e : DomainPreimage Φ s r) :=
 domain_preimage_mul_left_one Φ s r e ∧ DomainPreimageMulRightOne Φ s r e


private def DomainPreimageMulOne [DomainMulUnion Φ s] := { e : DomainPreimage Φ s r // DomainPreimageMulOne' Φ s r e }


-- TODO: Should I prefer `Coe` here? It would probably work
instance [DomainMulUnion Φ s] : CoeOut (DomainPreimageMulOne Φ s r) (DomainPreimage Φ s r) where
  coe e := e.val


-- Note that at this point I'm clamboring for better names
class DomainPreimageMulOneClass extends DomainMulUnion Φ s where
  one (r : Set s) : DomainPreimageMulOne Φ s r


-- Tangential proof for fun
lemma domain_preimage_left_one_eq_right_one
    [DomainMulUnion Φ s]
    (eLeft : DomainPreimage Φ s r)
    (h_left : domain_preimage_mul_left_one Φ s r eLeft)
    (eRight : DomainPreimage Φ s r)
    (h_right : DomainPreimageMulRightOne Φ s r eRight)
    : (eLeft : Φ) = eRight
    := by
  have h_val : eLeft.val = eRight.val := by
    conv =>
      rhs
      rw [← h_left eRight]
    conv =>
      lhs
      rw [← h_right eLeft]
  exact h_val
  done


-- Seems like it would be necessary for choice procedures, but haven't needed to invoke this
-- yet...
lemma domain_preimage_left_one_unique
    [DomainMulUnion Φ s]
    (e₁ : DomainPreimageMulOne Φ s r)
    (e₂ : DomainPreimageMulOne Φ s r)
    : (e₁ : Φ) = e₂
    := by
  let h₁_left := e₁.property.left
  let h₂_right := e₂.property.right
  conv =>
    rhs
    rw [← h₁_left e₂]
  conv =>
    lhs
    rw [← h₂_right e₁]
  done


-- TODO: Is this more convenient as a class for making a `Monoid` instance?
private def DomainPreimageMonoid [DomainMulUnion Φ s] := Π r : Set s, DomainPreimageMulOne Φ s r


-- TODO: Wow, this is syntactically horrible; speaks an issue in my comfort with type classes and possibly in the implementation
-- strategy we have set up right now
instance
    [instSemigroup : Semigroup Φ]
    [instDomainPreimageMulOneClass : @DomainPreimageMulOneClass Φ s instSemigroup]
    : Monoid (@DomainPreimage Φ s r instDomainPreimageMulOneClass.toDomain)
    where
  one :=
    let e := @DomainPreimageMulOneClass.one Φ s instSemigroup instDomainPreimageMulOneClass r
    e.val
  one_mul :=
    let e := @DomainPreimageMulOneClass.one Φ s instSemigroup instDomainPreimageMulOneClass r
    e.property.left
  mul_one :=
    let e := @DomainPreimageMulOneClass.one Φ s instSemigroup instDomainPreimageMulOneClass r
    e.property.right


private def DomainMarginalize
    [Domain Φ s]
    [Marginalize Φ s]
    : Prop
    :=
  ∀ x : Set s, ∀ φ : Φ, Domain.domain (Marginalize.marginalize φ x) = x


private def MarginalizeTrans
    [Marginalize Φ s]
    :=
  ∀ φ : Φ, ∀ x y : Set s, x ⊆ y →  Marginalize.marginalize φ x = Marginalize.marginalize (Marginalize.marginalize φ y) x


private def MulMarginalize
    [instDomain : Domain Φ s]
    [Marginalize Φ s]
    :=
  ∀ φ ψ : Φ,
  -- Using instance here so that other instances can be inferred
  let r₁ := instDomain.domain φ
  let r₂ := Domain.domain ψ
  let r₃ := r₁ ∩ r₂
  Marginalize.marginalize (φ * ψ) r₁ = φ * (Marginalize.marginalize ψ r₃)


-- TODO: There's something wrong with the naming convention here
private def mulOnes
    [DomainMulUnion Φ s]
    (x : Set s)
    (ex : DomainPreimageMulOne Φ s x)
    (y : Set s)
    (ey : DomainPreimageMulOne Φ s y)
    : DomainPreimage Φ s (x ∪ y)
    :=
  let ex' := ex.val.val
  let ey' := ey.val.val
  let hx : Domain.domain (ex : Φ) = x := (ex : DomainPreimage Φ s x).property
  let hy : Domain.domain (ey : Φ) = y := (ey : DomainPreimage Φ s y).property
  let h : Domain.domain ((ex : Φ) * ey) = x ∪ y := by
    rw [DomainMulUnion._mul_union, hx, hy]
  ⟨ex' * ey', h⟩


private def MulOnesOne
    [DomainMulUnion Φ s]
    :=
  ∀ x : Set s,
  ∀ ex : DomainPreimageMulOne Φ s x,
  ∀ y : Set s,
  ∀ ey : DomainPreimageMulOne Φ s y,
  DomainPreimageMulOne' Φ s (x ∪ y) (mulOnes Φ s x ex y ey)


/-
JK:
We define now formally a valuation algebra by a system of axioms.
-/
class LabeledValuationAlgebra extends DomainMulUnion Φ s, Marginalize Φ s where
  /-
  JK:
  Axiom 1, "Semigroup"
  Axiom (1) says that Φ is a commutative semigroup under combination and that a neutral element is adjoined for every sub-semigroup Φₛ of valuations for s. Note that the neutral element is unique. If there would be a second one, say e'ₛ, then we have e'ₛ = eₛ ⊗ e'ₛ = eₛ.
  -/
  domain_preimage_monoid := DomainPreimageMonoid Φ s
  _jk_axiom_1 := domain_preimage_monoid
  _jk_semigroup := domain_preimage_monoid
  /-
  JK:
  Axiom 2, "Labeling"
  The labeling axiom says that under combination the domains of the factors are joined.
  -/
  domain_mul_union := _mul_union
  _jk_axiom_2 := domain_mul_union
  _jk_labelling := domain_mul_union
  /-
  JK:
  Axiom 3, "Marginalization"
  The marginalization axioms says that marginalization to a domain x yields a valuation for this domain.
  -/
  domain_marginalize : DomainMarginalize Φ s
  _jk_axiom_3 := domain_marginalize
  _jk_marginalization := domain_marginalize
  /-
  JK:
  Axiom 4, "Transitivity"
  The transitivity axiom tells us that marginalization to some domain x can be done in two (or more) steps by intermediate marginalization to intermediate domains.
  -/
  marginalize_trans : MarginalizeTrans Φ s
  _jk_axiom_4 := marginalize_trans
  _jk_transitivity := marginalize_trans
  /-
  JK:
  Axiom 5, "Combination"
  The combination axioms assures that in order to marginalize to a domain of one of the factors of a combination it is not necessary to compute first the combination, but that we can as well first marginalize the other factor to the domain of the first one and then combine the two valuations. It means that we need in fact not leave the domains of the two factors to compute the marginal of the combination. It is essentially this axiom which allows local computation.
  -/
  mul_marginalize : MulMarginalize Φ s
  _jk_axiom_5 := mul_marginalize
  _jk_combination := mul_marginalize
  /-
  JK:
  Axiom 6, "Neutrality"
  The neutrality axiom finally specifies combination of neutral elements to give neutral elements.
  -/
  mulOnesOne : MulOnesOne Φ s
  _jk_axiom_6 := mulOnes
  _jk_neutrality := mulOnes
