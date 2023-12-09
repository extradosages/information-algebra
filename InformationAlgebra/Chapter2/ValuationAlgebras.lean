import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Subsemigroup.Basic
import Mathlib.Tactic.LibrarySearch

/-
TODO: Look up module docstring conventions
-/

namespace ValuationAlgebras


section


variable
  (Φ s : Type)
  [instCommSemigroup : CommSemigroup Φ]
  (x y : Set s)


-- Combining valuations

-- Getting a valuation's domain
class Domain where
  domain : Φ → Set s


notation:10000 "ð " => Domain.domain


-- Preimages of domains
def DomainPreimage [Domain Φ s] := { φ : Φ // ð φ = x }

-- Surprised that there isn't a generic coercion from a subtype to the og type...
-- TODO: Using `CoeOut` here because `(DomainPreimage Φ s r)` is not concrete and `Coe` requires
-- that that argument be concrete; this was an uninformed choice, am I doing something wrong?
instance [Domain Φ s] : CoeOut (DomainPreimage Φ s x) Φ where
  coe φ := φ.val


-- Combining valuations
infix:70 " ⊗ " => (· * ·)


class DomainMulUnion extends Domain Φ s where
  domain_mul_union : ∀ φ ψ : Φ, domain (φ ⊗ ψ) = ð φ ∪ ð ψ


/-
The preimage of any "mul union" domain is closed under multiplication.
-/
lemma preimage_domain_mul_closed
    [inst : DomainMulUnion Φ s]
    (φ : DomainPreimage Φ s x)
    (ψ : DomainPreimage Φ s x)
    -- At this point `⊗` hasn't formally been defined as
    -- heterogenous multiplication between preimages, only in `Φ`
    : ð ((φ : Φ) ⊗ (ψ : Φ)) = x
    := by
  have hφ : ð (φ : Φ) = x := φ.property
  have hψ : ð (ψ : Φ) = x := ψ.property
  let h := inst.domain_mul_union φ ψ
  rw [h, hφ, hψ]
  exact Set.union_self x
  done


instance (priority := high) [DomainMulUnion Φ s] : Mul (DomainPreimage Φ s r) where
  mul φ ψ := ⟨(φ : Φ) ⊗ (ψ : Φ), preimage_domain_mul_closed Φ s r φ ψ⟩


instance [DomainMulUnion Φ s] : CommSemigroup (DomainPreimage Φ s r) where
  mul_assoc := by
    intros φ ψ ϕ
    apply Subtype.ext_iff_val.mpr
    apply Semigroup.mul_assoc
  mul_comm := by
    intros φ ψ
    apply Subtype.ext_iff_val.mpr
    apply CommSemigroup.mul_comm


instance (priority := mid)
    [DomainMulUnion Φ s]
    (x y : Set s)
    : HMul (DomainPreimage Φ s x) (DomainPreimage Φ s y) (DomainPreimage Φ s (x ∪ y))
    where
  hMul φ ψ := ⟨
    (φ : Φ) ⊗ (ψ : Φ),
    by
      convert DomainMulUnion.domain_mul_union (φ : Φ) (ψ : Φ)
      · rw [φ.property]
      · rw [ψ.property]
  ⟩


class DomainPreimageMulOne extends DomainMulUnion Φ s where
  one r : DomainPreimage Φ s r
  mul_one r : ∀ φ : DomainPreimage Φ s r, (one r) * φ = φ


set_option quotPrecheck false
notation:10000 "e " => fun x => (DomainPreimageMulOne.one x : DomainPreimage Φ s x)


--  Marginalizing a valuation
class Marginalize where
  -- TODO: Actually, JK has the type more like `Π φ : Φ, 𝒫 (domain φ) → Φ`
  -- Maybe this doesn't even matter
  marginalize: Φ → Set s → Φ


infixl:70 " ↓ " => Marginalize.marginalize


private def DomainMarginalize
    [Domain Φ s]
    [Marginalize Φ s]
    : Prop
    :=
  ∀ x : Set s, ∀ φ : Φ, ð (φ ↓ x) = x


private def MarginalizeTrans
    [Marginalize Φ s]
    :=
  ∀ φ : Φ,
  ∀ x y : Set s,
  x ⊆ y →  φ ↓ x = (φ ↓ y) ↓ x


private def MulMarginalize
    [Domain Φ s]
    [Marginalize Φ s]
    :=
  ∀ φ ψ : Φ,
  (φ ⊗ ψ) ↓ (ð φ : Set s) = φ ⊗ (ψ ↓ (ð φ ∩ ð ψ : Set s))


private def MulOnesOne
    [DomainPreimageMulOne Φ s]
    :=
  ∀ x : Set s,
  ∀ y : Set s,
  e x ⊗ e y = e (x ∪ y)

/-
JK:
We define now formally a valuation algebra by a system of axioms.
-/
class ValuationAlgebra extends DomainPreimageMulOne Φ s, Marginalize Φ s where
  /-
  JK:
  Axiom 1, "Semigroup"
  Axiom (1) says that Φ is a commutative semigroup under combination and that a neutral element is adjoined for every sub-semigroup Φₛ of valuations for s. Note that the neutral element is unique. If there would be a second one, say e'ₛ, then we have e'ₛ = eₛ ⊗ e'ₛ = eₛ.
  -/
  -- Via `DomainPreimageMulOne.one`, `DomainPreimageMulOne.mul_one`, the `DomainPreimage` instance of `CommSemigroup`

  /-
  JK:
  Axiom 2, "Labeling"
  The labeling axiom says that under combination the domains of the factors are joined.
  -/
  -- Via `DomainMulUnion.domain_mul_union`

  /-
  JK:
  Axiom 3, "Marginalization"
  The marginalization axioms says that marginalization to a domain x yields a valuation for this domain.
  -/
  domain_marginalize : DomainMarginalize Φ s

  /-
  JK:
  Axiom 4, "Transitivity"
  The transitivity axiom tells us that marginalization to some domain x can be done in two (or more) steps by intermediate marginalization to intermediate domains.
  -/
  marginalize_trans : MarginalizeTrans Φ s

  /-
  JK:
  Axiom 5, "Combination"
  The combination axioms assures that in order to marginalize to a domain of one of the factors of a combination it is not necessary to compute first the combination, but that we can as well first marginalize the other factor to the domain of the first one and then combine the two valuations. It means that we need in fact not leave the domains of the two factors to compute the marginal of the combination. It is essentially this axiom which allows local computation.
  -/
  mul_marginalize : MulMarginalize Φ s

  /-
  JK:
  Axiom 6, "Neutrality"
  The neutrality axiom finally specifies combination of neutral elements to give neutral elements.
  -/
  mul_ones_one : MulOnesOne Φ s
