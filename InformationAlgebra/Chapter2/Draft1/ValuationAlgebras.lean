import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Subsemigroup.Basic
import Mathlib.Tactic.LibrarySearch

/-
TODO: Look up module docstring conventions
-/

namespace ValuationAlgebras1

variable
  (Φ s : Type)
  [instCommSemigroup : CommSemigroup Φ]


-- Getting a valuation's domain
class Domain where
  domain (φ : Φ) : Set s
  -- TODO: Get this to work
  -- domainPreimage (x : Set s) := { φ : Φ // domain φ = x }


notation:10000 "ð " => Domain.domain


-- Preimages of domains
def DomainPreimage {s : Type} [Domain Φ s] (x : Set s) := { φ : Φ // ð φ = x }


local notation:10000 "ð⁻¹ " => DomainPreimage


instance [Domain Φ s] (x : Set s) : Domain (ð⁻¹ Φ x) s where
  domain _ := x


-- Surprised that there isn't a generic coercion from a subtype to the og type...
-- TODO: Using `CoeOut` here because `(DomainPreimage Φ s r)` is not concrete and `Coe` requires
-- that that argument be concrete; this was an uninformed choice, am I doing something wrong?
instance [Domain Φ s] (x : Set s) : CoeOut (ð⁻¹ Φ x) Φ where
  coe φ := φ.val


-- Combining valuations
infix:70 " ⊗ " => HMul.hMul


class DomainMulUnion extends Domain Φ s where
  domain_mul_union (φ ψ : Φ) : domain (φ ⊗ ψ) = ð φ ∪ ð ψ


-- TODO: We may want to explore using only `HMul` and getting `Mul`
-- for free from a default instance
instance (priority := mid)
    [DomainMulUnion Φ s]
    {x y : Set s}
    : HMul (ð⁻¹ Φ x) (ð⁻¹ Φ y) (ð⁻¹ Φ (x ∪ y))
    where
  hMul φ ψ := by
    let ϕ := (φ : Φ) ⊗ (ψ : Φ)
    have h : ð ϕ = x ∪ y := by
      rw [DomainMulUnion.domain_mul_union (φ : Φ) (ψ : Φ), φ.prop, ψ.prop]
      done
    exact ⟨ϕ, h⟩
    done


instance (priority := high)
    [DomainMulUnion Φ s]
    {x : Set s}
    : Mul (ð⁻¹ Φ x)
    where
  mul φ ψ  := by
    let ϕ := φ ⊗ ψ
    have h : ð (ϕ : Φ) = x := by
      rw [ϕ.property]
      exact Set.union_self x
      done
    exact ⟨ϕ, h⟩
    done


instance [DomainMulUnion Φ s] (x : Set s) : CommSemigroup (ð⁻¹ Φ x) where
  mul_assoc φ ψ ϕ := by
    apply Subtype.ext_iff_val.mpr
    apply Semigroup.mul_assoc
    done
  mul_comm φ ψ := by
    apply Subtype.ext_iff_val.mpr
    apply CommSemigroup.mul_comm
    done


--  Marginalizing a valuation
class Marginalize extends DomainMulUnion Φ s where
  marginalize (φ : Φ) (x : Set s) (h : x ⊆ ð φ) : Φ


notation:10000 "(" φ " ↓ " x ", " h ")"  => Marginalize.marginalize φ x h


class DomainMarginalize extends Marginalize Φ s where
  domain_marginalize {φ : Φ} {x : Set s} (h : x ⊆ ð φ) : ð (φ ↓ x, h) = x


private lemma marginalize_trans_lhs
    {Φ s : Type}
    [CommSemigroup Φ]
    [DomainMarginalize Φ s]
    {φ : Φ}
    {x y : Set s}
    (hx : x ⊆ ð φ)
    (hy : y ⊆ x)
    : y ⊆ ð φ
    :=
  subset_trans hy hx


private lemma marginalize_trans_rhs
    {Φ s : Type}
    [CommSemigroup Φ]
    [DomainMarginalize Φ s]
    {φ : Φ}
    {x y : Set s}
    (hx : x ⊆ ð φ)
    (hy : y ⊆ x)
    : y ⊆ ð (φ ↓ x, hx)
    := by
  rw [DomainMarginalize.domain_marginalize]
  exact hy
  done


private lemma mul_marginalize_lhs
    {Φ s : Type}
    [CommSemigroup Φ]
    [DomainMulUnion Φ s]
    (φ ψ : Φ)
    : (ð φ : Set s) ⊆ ð (φ ⊗ ψ)
    := by
  rw [DomainMulUnion.domain_mul_union]
  exact Set.subset_union_left (ð φ) (ð ψ)
  done


private lemma mul_marginalize_rhs
    {Φ s : Type}
    [Domain Φ s]
    (φ ψ : Φ)
    : ð φ ∩ ð ψ ⊆ (ð ψ : Set s)
    := Set.inter_subset_right (ð φ) (ð ψ)


class DomainPreimageMulOne extends DomainMarginalize Φ s where
  one (x : Set s) : ð⁻¹ Φ x
  mul_one (x : Set s) (φ : ð⁻¹ Φ x) : (one x) ⊗ φ = φ


notation:10000 "e " => DomainPreimageMulOne.one

/-
JK:
We define now formally a valuation algebra by a system of axioms.
-/
class ValuationAlgebra extends DomainPreimageMulOne Φ s where
  /-
  JK:
  Axiom 1, "Semigroup"
  Axiom (1) says that Φ is a commutative semigroup under combination and that a neutral element is adjoined for every sub-semigroup Φₛ of valuations for s. Note that the neutral element is unique. If there would be a second one, say e'ₛ, then we have e'ₛ = eₛ ⊗ e'ₛ = eₛ.
  -/
  -- Via `CommSemigroup.*`, and `DomainPreimageMulOne.*`

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
  -- Via `DomainMarginalize.domain_marginalize`

  /-
  JK:
  Axiom 4, "Transitivity"
  The transitivity axiom tells us that marginalization to some domain x can be done in two (or more) steps by intermediate marginalization to intermediate domains.
  -/
  marginalize_trans {φ : Φ} {x y : Set s} (hx : x ⊆ ð φ) (hy : y ⊆ x) :
    (φ ↓ y, marginalize_trans_lhs hx hy) = ((φ ↓ x, hx) ↓ y, marginalize_trans_rhs hx hy)

  /-
  JK:
  Axiom 5, "Combination"
  The combination axioms assures that in order to marginalize to a domain of one of the factors of a combination it is not necessary to compute first the combination, but that we can as well first marginalize the other factor to the domain of the first one and then combine the two valuations. It means that we need in fact not leave the domains of the two factors to compute the marginal of the combination. It is essentially this axiom which allows local computation.
  -/
  mul_marginalize (φ ψ : Φ) :
    (φ ⊗ ψ ↓ (ð φ : Set s), mul_marginalize_lhs φ ψ) = φ ⊗ (ψ ↓ (ð φ ∩ ð ψ : Set s), mul_marginalize_rhs φ ψ)

  /-
  JK:
  Axiom 6, "Neutrality"
  The neutrality axiom finally specifies combination of neutral elements to give neutral elements.
  -/
  mul_ones_one (x y : Set s) :
    (e x : ð⁻¹ Φ x) ⊗ (e y : ð⁻¹ Φ y) = (e (x ∪ y) : ð⁻¹ Φ (x ∪ y))


end ValuationAlgebras1
