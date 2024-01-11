import Mathlib


namespace ValuationAlgebras


variable
  {ι : Type*}
  [Lattice ι]
  (A : ι → Type*)


class ValuationAlgebra where
  /-- Cast terms of one grade to another when those grades can be equated -/
  cast (h : i = j) : A i → A j
  /-- Reflexivity casts to the identity -/
  cast_rfl (x : A i) : cast rfl x = x
  /-- Inter-grade multiplication -/
  mul : A i → A j → A (i ⊔ j)
  /-- Inter-grade multiplication is commutative -/
  mul_comm (x : A i) (y : A j) : cast sup_comm (mul x y) = mul y x
  /-- Inter-grade multiplication is associative -/
  mul_assoc (x : A i) (y : A j) (z : A k) : cast sup_assoc (mul (mul x y) z) = mul x (mul y z)
  /-- Each grade has a `one` -/
  one i : A i
  /-- Intra-grade multiplication by the grade's `one` is the identity -/
  mul_one (x : A i) : cast sup_idem (mul x (one i)) = x
  /-- Inter-grade multiplication of `one` elements produces a `one` element -/
  mul_one_one : mul (one i) (one j) = one (i ⊔ j)



variable
  {A : ι → Type*}
  [ValuationAlgebra A]


infixl:70 " ↓ " => ValuationAlgebra.margin


instance : HMul (A i) (A j) (A (i ⊔ j)) where
  hMul x y := ValuationAlgebra.mul x y


variable
  {i j : ι}
  (x : A i)
  (y : A j)


@[simp]
def statement2p1p1LHS : A (i ⊓ j) := (x * y) ↓ τ (i ⊓ j : ι)
@[simp]
def statement2p1p1RHS : A ((i ⊓ j) ⊔ (i ⊓ j)) := (x ↓ τ (i ⊓ j : ι)) * (y ↓ τ (i ⊓ j : ι))
def statement2p1p1Cast : A ((i ⊓ j) ⊔ (i ⊓ j)) → A (i ⊓ j) := ValuationAlgebra.cast sup_idem
@[simp]
def Statement2p1p1 := statement2p1p1LHS x y = statement2p1p1Cast (statement2p1p1RHS x y)


lemma proof_2p1p1 : Statement2p1p1 x y := by
  simp only [statement2p1p1LHS, statement2p1p1RHS, Statement2p1p1]
  conv =>
    lhs
    whnf
    rw [← ValuationAlgebra.margin_trans (x * y) (τ i) (τ (i ⊓ j) : Principal i)]
  done
