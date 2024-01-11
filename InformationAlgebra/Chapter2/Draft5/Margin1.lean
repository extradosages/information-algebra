import Mathlib


namespace Margin


variable
  {ι : Type*}
  [Lattice ι]
  (A : ι → Type*)


def Principal (i : ι) := { j : ι // j ≤ i }


def principalTop (i : ι) : Principal i := ⟨i, le_refl i⟩
abbrev τ (i : ι) := principalTop i


example (i : ι) : Principal i := τ i
example (i j : ι) : Principal (i ⊓ j) := τ (i ⊓ j)


instance instCoeTauCompute : CoeDep (Principal (i : ι)) (τ i) ι where
  coe := i


instance instCoePrincipalToLattice (i : ι) : CoeHead (Principal i) ι where
  coe j := j.val


example {i : ι} (k : Principal i) : ι := k


instance instCoeInfComm : CoeHead (Principal (i ⊓ j : ι)) (Principal (j ⊓ i)) where
  coe k := ⟨k, le_trans k.property (Eq.le inf_comm)⟩


example {i j : ι} (k : Principal (i ⊓ j)) : Principal (j ⊓ i) := k
example (i j : ι) : Principal (j ⊓ i) := principalTop (i ⊓ j)


instance instCoeSupComm : CoeHead (Principal (i ⊔ j : ι)) (Principal (j ⊔ i)) where
  coe k := ⟨k, le_trans k.property (Eq.le sup_comm)⟩


example {i j : ι} (k : Principal (i ⊔ j)) : Principal (j ⊔ i) := k
example (i j : ι) : Principal (j ⊔ i) := principalTop (i ⊔ j)


instance instCoeInfAssoc : CoeHead (Principal (i ⊓ j ⊓ k : ι)) (Principal (i ⊓ (j ⊓ k))) where
  coe l := ⟨l, le_trans l.property (Eq.le inf_assoc)⟩


instance instCoeSupAssoc : CoeHead (Principal (i ⊔ j ⊔ k : ι)) (Principal (i ⊔ (j ⊔ k))) where
  coe l := ⟨l, le_trans l.property (Eq.le sup_assoc)⟩


instance instCoeSupIdem : CoeHead (Principal (i ⊔ i : ι)) (Principal i) where
  coe k := ⟨k, le_trans k.property (Eq.le sup_idem)⟩


instance instCoeInfIdem : CoeHead (Principal (i : ι)) (Principal (i ⊓ i)) where
  coe k := ⟨k, le_trans k.property (Eq.ge inf_idem)⟩


instance instCoeLeSupLeft : Coe (Principal (i : ι)) (Principal (i ⊔ j)) where
  coe k := ⟨k, le_trans k.property le_sup_left⟩


instance instCoeInfLeLeft : CoeOut (Principal (i ⊓ j : ι)) (Principal i) where
  coe k := ⟨k.val, le_trans k.property inf_le_left⟩


set_option maxHeartbeats 1000000 in
-- set_option trace.Meta.synthInstance true in
class Margin where
  /-- Marginalization over sub-grades -/
  margin : A i → (j : Principal i) → A j
  /-- Marginalization respects transitivity of sub-grades -/
  margin_trans (x : A i) (j : Principal i) (k : Principal (j : ι)) : margin (margin x j) k = margin x ⟨k, le_trans k.property j.property⟩
  /-- Marginalization distributes across multiplication in a particular way -/
  margin_mul [HMul (A i) (A j) (A (i ⊔ j))] (x : A i) (y : A j) : margin (x * y) (τ i) = cast sup_inf_self (x * (margin y (τ (i ⊓ j))))