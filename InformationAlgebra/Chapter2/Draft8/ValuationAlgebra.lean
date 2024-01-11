import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Sigma.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic


variable
  {D : Type*}
  [Preorder D]


structure ValuationAlgebra (Φ : D → Type*) where mk' ::
  grade : D
  val : Φ grade
  margin : D
  le : margin ≤ grade


def ValuationAlgebra.mk {Φ : D → Type*} (φ : Φ x) : ValuationAlgebra Φ :=
  { grade := x, val := φ, margin := x, le := le_refl x }


def ValuationAlgebra.mkMargin {Φ : D → Type*} (φ : Φ x) (p : y ≤ x) : ValuationAlgebra Φ :=
  { grade := x, val := φ, margin := y, le := p }


section Defs


variable (Φ : D → Type*)


/-- A graded version of `One`, in which every grade has a `one`-/
class GOne where
  one x : Φ x


def gOne {Φ : D → Type*} [GOne Φ] (x : D) : ValuationAlgebra Φ := ValuationAlgebra.mk x (GOne.one x)



notation:70 "e " x => gOne x


/-- A graded version of `Mul`. Multiplication joins of grades. -/
class GMul [DistribLattice D] where
  mul : Φ x → Φ y → Φ (x ⊔ y)


example [GMul Φ] :


infixl:70 (priority := high) " ⊗ " => GMul.mul


/-- `GMul` implies `Mul (ValuationAlgebra Φ)` -/
instance GMul.toMul [DistribLattice D] [GMul Φ] : Mul (ValuationAlgebra Φ) :=
  ⟨fun ⟨x, φ, x', _⟩ ⟨y, ψ, y', _⟩ ↦ ⟨_, GMul.mul φ ψ, _, _⟩⟩


-- TODO: Why do we have this?
theorem mk_mul_mk [DistribLattice D] [GMul Φ] (φ : Φ x) (ψ : Φ y) :
    mk x φ * mk y ψ = mk (x ⊔ y) (φ ⊗ ψ) :=
  rfl


class GCommSemigroup [DistribLattice D] extends GMul Φ where
  /-- Multiplication is associative. -/
  mul_assoc (a b c : ValuationAlgebra Φ) : a * b * c = a * (b * c)
  /-- Multiplication is commutative. -/
  mul_comm (a b : ValuationAlgebra Φ) : a * b = b * a


class GLocalMonoid [DistribLattice D] extends GOne Φ, GMul Φ where
  /-- Multiplication by `one` is the identity -/
  mul_one (a : ValuationAlgebra Φ) : a * (e (ð a)) = a
  mul_one_one : (e x : ValuationAlgebra Φ) * (e y) = (e (x ⊔ y))


class GWeakMargin [LE D] where
  margin : (φ : Φ x) → (p : y ≤ x) → Φ y


infixl:70 " ↓ " => GWeakMargin.margin


def margin [LE D] [GWeakMargin Φ] (φ : ValuationAlgebra Φ) (p : y ≤ ð φ) := (GWeakMargin.margin φ p)


class GMarginWeakTrans [LE D] extends GWeakMargin Φ where
  margin_weak_trans (φ : Φ x) (p : y ≤ x) (q : z ≤ y) (r : z ≤ x) : (φ ↓ p) ↓ q = (φ ↓ r)


class GMarginWeakMul [DistribLattice D] [GCommSemigroup Φ] where
  margin_weak_mul (φ ψ : ValuationAlgebra Φ) (p : z ≤ (ð φ) ⊔ (ð ψ)) : (φ * ψ)
