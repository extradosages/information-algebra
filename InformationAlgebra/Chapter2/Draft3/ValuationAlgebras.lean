import Mathlib


namespace ValuationAlgebras


variable
  {D : Type*}
  (Φ : D → Type*)


def Valuation :=
  Sigma Φ


/-- The `label` of a valuation is its domain -/
def label {Φ : D → Type*} (φ : Valuation Φ) := φ.fst


@[inherit_doc]
notation:10000 "ð " => label


class DomainMul [Sup D] where
  /-- Multiplication map `mul` across domains -/
  mul : Φ r → Φ s → Φ (r ⊔ s)


@[inherit_doc]
infix:10000 " ⊚ " => DomainMul.mul


instance DomainMul.toHMul [Sup D] [DomainMul Φ] : HMul (Φ r) (Φ s) (Φ (r ⊔ s)) where
  hMul φ ψ := DomainMul.mul φ ψ


instance (priority := high) DomainMul.toMul  [Sup D] [DomainMul Φ] : Mul (Valuation Φ) where
  mul φ ψ := ⟨_, DomainMul.mul φ.snd ψ.snd⟩


class DomainCommSemigroup [Sup D] extends DomainMul Φ where
  /-- Multiplication is associative -/
  mul_assoc (φ ψ ϕ : Valuation Φ) : φ * ψ * ϕ = φ * (ψ * ϕ)
  /-- Multiplication is commutative -/
  mul_comm (φ ψ : Valuation Φ) : φ * ψ = ψ * φ


instance DomainCommSemigroup.toCommSemigroup [Sup D] [DomainCommSemigroup Φ] : CommSemigroup (Valuation Φ)
    where
  mul_assoc := DomainCommSemigroup.mul_assoc
  mul_comm := DomainCommSemigroup.mul_comm


class DomainOne where
  /-- The term `one` of each grade -/
  one r : Φ r


class DomainNeutrality [Sup D] extends DomainMul Φ, DomainOne Φ where
  /-- The product of two `one`s is a `one` -/
  neutrality : DomainMul.mul (one s) (one r) = one (s ⊔ r)


section SubDomain


variable
  [PartialOrder D]
  (r : D)


def SubDomain := { s : D // s ≤ r }


instance : CoeOut (SubDomain r) D where
  coe r := r.val


instance : PartialOrder (SubDomain r) where
  le s t := (s : D) ≤ t
  le_refl s := Preorder.le_refl (s : D)
  le_trans s t u := Preorder.le_trans (s : D) t u
  le_antisymm s t := by
    intros hst hts
    apply Subtype.ext
    apply PartialOrder.le_antisymm
    · exact hst
    · exact hts
    done

end SubDomain


section Coe


class DomainTerm (r : D) where
  term := r


class DomainTermSup (r s : D) where
  left := r
  right := s


instance [SemilatticeSup D] (r s : D) [DomainTermSup r s] : DomainTerm (r ⊔ s) where


instance [SemilatticeSup D] (r s : D) [DomainTerm (r ⊔ s)] : DomainTermSup r s where
  

class DomainTermInf (r s : D) where
  left := r
  right := s


instance [SemilatticeInf D] (r s : D) [DomainTermInf r s] : DomainTerm (r ⊓ s) where


instance [SemilatticeInf D] (r s : D) [DomainTerm (r ⊓ s)] : DomainTermInf r s where


instance [SemilatticeSup D] (r s : D) [DomainTerm (r ⊔ s)] : DomainTerm (s ⊔ r) where


instance [SemilatticeSup D] (r s t : D) [DomainTerm (r ⊔ s ⊔ t)] : DomainTerm (r ⊔ (s ⊔ t)) where


instance [SemilatticeSup D] (r s t : D) [DomainTerm (r ⊔ (s ⊔ t))] : DomainTerm (r ⊔ s ⊔ t) where


instance [SemilatticeSup D] (r : D) [DomainTerm (r ⊔ r)] : DomainTerm r where






instance [PartialOrder D] {r : D} (s : SubDomain r) : CoeOut (SubDomain s) (SubDomain r) where
  coe t := ⟨t.val, le_trans t.property s.property⟩


instance [PartialOrder D] {r : D} (s : SubDomain r) : CoeOut (SubDomain s) (SubDomain (s : D)) where
  coe t := ⟨t, t.property⟩


-- structure SubDomainLeCoe [PartialOrder D] (s t : D) where
--   val : SubDomain s
--   le : s ≤ t


-- instance [PartialOrder D] {s t : D} : CoeOut (SubDomainLeCoe s t) (SubDomain t) where
--   coe := fun ⟨u, h⟩ ↦ ⟨u, le_trans u.property h⟩


-- instance [SemilatticeSup D] {s t : D} : Coe (SubDomain s) (SubDomain (s ⊔ t)) where
--   coe u := SubDomainLeCoe.mk u (le_sup_left : s ≤ s ⊔ t)


-- instance [SemilatticeSup D] {s t : D} : Coe (SubDomain t) (SubDomain (s ⊔ t)) where
--   coe u := SubDomainLeCoe.mk u (le_sup_right : t ≤ s ⊔ t)


instance [SemilatticeInf D] {s t : D} : CoeDep D (s ⊓ t) (SubDomain s) where
  coe := ⟨s ⊓ t, inf_le_left⟩


instance [SemilatticeInf D] {s t : D} : CoeDep D (s ⊓ t) (SubDomain t) where
  coe := ⟨s ⊓ t, inf_le_right⟩


structure DomainEqCoe (s t : D) where
  val : Φ s
  eq : s = t


instance : CoeOut (DomainEqCoe Φ s t) (Φ t) where
  coe := fun ⟨φ, h⟩ ↦ Equiv.cast (congrArg Φ h) |>.toFun φ


end Coe


class Marginalize [PartialOrder D] where
  /-- Marginalize a valuation by a sub domain -/
  marginalize : Φ r → (s : SubDomain r) → Φ s


@[inherit_doc]
infixl:1000 " ↓ " => Marginalize.marginalize


class MarginalizeTrans [PartialOrder D] extends Marginalize Φ where
  marginalize_trans
      (φ : Φ r)
      (s : SubDomain r)
      (t : SubDomain s)
      :
      (marginalize φ t : Φ t) = marginalize (marginalize φ s : Φ s) t


private def StatementMarginalizeMul
    [Lattice D]
    [DomainMul Φ]
    [Marginalize Φ]
    (φ : Φ x)
    (ψ : Φ y)
    :
    Prop
    :=
  let lhs : Φ x := Marginalize.marginalize (DomainMul.mul φ ψ) ⟨x, le_sup_left⟩
  let ψ := Marginalize.marginalize ψ (⟨x ⊓ y, inf_le_right⟩ : SubDomain y)
  let rhs : Φ x := DomainEqCoe.mk (DomainMul.mul φ ψ) sup_inf_self
  lhs = rhs


class MarginalizeMul [Lattice D] extends DomainMul Φ, Marginalize Φ where
  marginalize_mul (φ : Φ r) (ψ : Φ s) : StatementMarginalizeMul Φ φ ψ


class ValuationAlgebra [Lattice D] extends DomainNeutrality Φ, DomainCommSemigroup Φ, MarginalizeTrans Φ, MarginalizeMul Φ where
  /-
  JK:
  Axiom 1, "Semigroup"
  Axiom (1) says that Φ is a commutative semigroup under combination and that a neutral element is adjoined for every sub-semigroup Φₛ of valuations for s. Note that the neutral element is unique. If there would be a second one, say e'ₛ, then we have e'ₛ = eₛ ⊗ e'ₛ = eₛ.
  -/
  -- Via `DomainCommSemigroup`, and `DomainOne`

  /-
  JK:
  Axiom 2, "Labeling"
  The labeling axiom says that under combination the domains of the factors are joined.
  -/
  -- Via the type of `DomainMul.mul`

  /-
  JK:
  Axiom 3, "Marginalization"
  The marginalization axioms says that marginalization to a domain x yields a valuation for this domain.
  -/
  -- Via the type of `Marginalize.marginalize`

  /-
  JK:
  Axiom 4, "Transitivity"
  The transitivity axiom tells us that marginalization to some domain x can be done in two (or more) steps by intermediate marginalization to intermediate domains.
  -/
  -- Via `MarginalizeTrans.marginalize_trans`

  /-
  JK:
  Axiom 5, "Combination"
  The combination axioms assures that in order to marginalize to a domain of one of the factors of a combination it is not necessary to compute first the combination, but that we can as well first marginalize the other factor to the domain of the first one and then combine the two valuations. It means that we need in fact not leave the domains of the two factors to compute the marginal of the combination. It is essentially this axiom which allows local computation.
  -/
  -- Via `MarginalizeMul.marginalize_mul`

  /-
  JK:
  Axiom 6, "Neutrality"
  The neutrality axiom finally specifies combination of neutral elements to give neutral elements.
  -/
  -- Via `DomainNeutrality.neutrality`


end ValuationAlgebras
