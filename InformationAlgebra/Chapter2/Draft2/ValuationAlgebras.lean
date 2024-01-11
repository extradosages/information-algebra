import Mathlib


namespace ValuationAlgebras2


variable
  (Variable : Type)


-- The set of all possible variables
def r : Set Variable := Set.univ


@[ext]
structure Domain where
  carrier : Set Variable


instance : SetLike (Domain Variable) Variable where
  coe s := s.carrier
  coe_injective' := by
    apply Domain.ext
    done


instance : Lattice (Domain Variable) where
  sup r t := ⟨r.carrier ∪ t.carrier⟩
  inf r t := ⟨r.carrier ∩ t.carrier⟩
  le_sup_left r t := by
    sorry
    done
  le_sup_right r t := by
    sorry
    done
  sup_le r t u := by
    sorry
    done
  inf_le_left r t := by
    sorry
    done
  inf_le_right r t := by
    sorry
    done
  le_inf r t u := by
    sorry
    done


section ex₁

example (r t : Domain Variable) := r ⊔ t

end ex₁


class Frame (Frameable : Type) where
  Frame : Frameable → Type


variable
  [Frame Variable]


-- JK: The type of frames of a variable is also called its "values"
abbrev JkValue (X : Variable) := Frame.Frame X


instance [Frame Variable] : Frame (Domain Variable)  where
  Frame s := (X : s) → Frame.Frame (X : Variable)


-- JK: The type of frames of a domain is also called its "configurations"
abbrev JkConfiguration (s : Domain Variable) := Frame.Frame s


variable
  (Valuation : Type)


class Label (Variable Valuation : Type) where
  /-- A label of a valuation is an assignment of a domain to a valuation -/
  label : Valuation → Domain Variable


notation:max "ð " => Label.label


variable
  [CommSemigroup Valuation]


@[inherit_doc]
infixl:1000 " ⊗ " => HMul.hMul


def DomainValuation {Variable : Type} [Label Variable Valuation] (r : Domain Variable) := { φ : Valuation // Label.label φ = r }


instance
    {Variable : Type}
    [Label Variable Valuation]
    (r : Domain Variable)
    :
    CoeOut (DomainValuation Valuation r) Valuation
    where
  coe φ := φ.val


instance {Variable : Type} [Label Variable Valuation] (r : Domain Variable) : Label Variable (DomainValuation Valuation r) where
  label φ := Label.label φ.val


class MulLabelUnion extends Label Variable Valuation where
  mul_label_union (φ ψ : Valuation) : label (φ ⊗ ψ) = label φ ⊔ label ψ


instance (priority := mid)
    [MulLabelUnion Variable Valuation]
    (s t : Domain Variable)
    : HMul
      (DomainValuation Valuation s)
      (DomainValuation Valuation t)
      (DomainValuation Valuation (s ⊔ t))
    where
  hMul φ ψ := by
    let ϕ : Valuation := (φ : Valuation) ⊗ (ψ : Valuation)
    have h : (Label.label ϕ : Domain Variable) = s ⊔ t := by
      rw [← φ.property, ← ψ.property]
      exact MulLabelUnion.mul_label_union (φ : Valuation) (ψ : Valuation)
      done
    exact ⟨ϕ, h⟩
    done


instance [MulLabelUnion Variable Valuation] (s : Domain Variable) : Coe (DomainValuation Valuation (s ⊔ s)) (DomainValuation Valuation s) where
  coe φ := by
    have h : ð (φ : Valuation) = s := by
      conv =>
        rhs
        rw [← (sup_idem : s ⊔ s = s)]
      rw [φ.property]
    exact ⟨φ, h⟩
    done


protected class MulOne {Variable : Type} [MulLabelUnion Variable Valuation] (s : Domain Variable) where
  one : DomainValuation Valuation s
  mul_one (φ : DomainValuation Valuation s) : φ ⊗ one = φ


/-- The type of domains which are subsets of a given domain -/
@[ext]
structure SubDomain {Variable : Type} (s : Domain Variable) where
  carrier : Domain Variable
  subset : carrier.carrier ⊆ s


instance (s : Domain Variable) : CoeOut (SubDomain s) (Domain Variable) where
  coe t := ⟨t.carrier⟩


instance (s : Domain Variable) : SetLike (SubDomain s) Variable where
  coe t := t.carrier
  coe_injective' := by
    intros x y
    simp
    apply SubDomain.ext
    done


class Marginalize extends Label Variable Valuation where
  marginalize (r : Domain Variable) (φ : DomainValuation Valuation r) (t : SubDomain r) : DomainValuation Valuation (t : Domain Variable)


notation:70 " ↓ " => Marginalize.marginalize


-- class ValuationAlgebra extends MulLabelUnion Variable Valuation, Marginalize Variable Valuation where
