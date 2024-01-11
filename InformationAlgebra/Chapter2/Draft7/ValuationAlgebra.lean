import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Sigma.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic


variable
  {D : Type*}


/-- A type alias of sigma types for valuation algebras -/
def ValuationAlgebra (Φ : D → Type*) :=
  Sigma Φ


namespace ValuationAlgebra


/-- Construct an element of a valuation algebra, a "valuation" -/
def mk {Φ : D → Type*} {x : D} (φ : Φ x) : ValuationAlgebra Φ :=
  Sigma.mk x φ


/-- Get the grade or "label" or an element of a valuation algebra -/
def label {Φ : D → Type*} (a : ValuationAlgebra Φ) :=
  Sigma.fst a


notation:70 "ð " a => label a


section Defs


variable (Φ : D → Type*)


/-- A graded version of `One`, in which every grade has a `one` -/
class GOne where
  one x : Φ x


def gOne {Φ : D → Type*} [GOne Φ] (x : D) : ValuationAlgebra Φ := ⟨x, GOne.one x⟩


example  [GOne Φ] (a : ValuationAlgebra Φ) : ValuationAlgebra Φ := gOne a.fst


notation:70 "e " x => gOne x


/-- A graded version of `Mul`. Multiplication joins of grades -/
class GMul [SemilatticeSup D] where
  mul : Φ x → Φ y → Φ (x ⊔ y)


infixl:70 (priority := high) " ⊗ " => GMul.mul


/-- `GMul` implies `Mul (ValuationAlgebra Φ)` -/
instance GMul.toMul [SemilatticeSup D] [GMul Φ] : Mul (ValuationAlgebra Φ) where
  mul := fun ⟨_, φ⟩ ⟨_, ψ⟩ ↦ ⟨_, φ ⊗ ψ⟩


theorem mk_mul_mk [SemilatticeSup D] [GMul Φ] (φ : Φ x) (ψ : Φ y) :
    mk φ * mk ψ = mk (φ ⊗ ψ) :=
  rfl


class GCommSemigroup [SemilatticeSup D] extends GMul Φ where
  /-- Multiplication is associative -/
  mul_assoc (a b c : ValuationAlgebra Φ) : a * b * c = a * (b * c)
  /-- Multiplication is commutative -/
  mul_comm (a b : ValuationAlgebra Φ) : a * b = b * a

instance GCommSemigroup.toSemigroup [SemilatticeSup D] [GCommSemigroup Φ] : CommSemigroup (ValuationAlgebra Φ) where
  mul_assoc := GCommSemigroup.mul_assoc
  mul_comm := GCommSemigroup.mul_comm


class GLocalMonoid [SemilatticeSup D] extends GOne Φ, GMul Φ where
  /-- Multiplication by `one` is the identity -/
  mul_one (a : ValuationAlgebra Φ) : a * (e (ð a)) = a
  /-- Multiplication of `one`s produces a `one` -/
  mul_one_one : (e x : ValuationAlgebra Φ) * (e y) = (e (x ⊔ y))


class GMargin [LE D] where
  /-- Marginalization of a valuation -/
  margin : (φ : Φ x) → (y : D) → (p : y ≤ x) → Φ y


notation:70 "(" φ " ↓ " y ", " p ")" => GMargin.margin φ y p


def StrongMarginTransStatement {Φ : D → Type*} [LE D] [GMargin Φ] (φ : Φ x) (y z : D) (p : y ≤ x) (q : z ≤ y) (r : z ≤ x) := ((φ ↓ y, p) ↓ z, q) = (φ ↓ z, r)
def StrongMarginMulStatement {Φ : D → Type*} [Lattice D] [GCommSemigroup Φ] [GMargin Φ] (φ : Φ x) (ψ : Φ y) (p : x ≤ x ⊔ y) (q : x ⊓ y ≤ y) (r : x ⊔ x ⊓ y = x) :=  (φ ⊗ ψ ↓ x, p) = r ▸ (φ ⊗ (ψ ↓ x ⊓ y, q))


class GStrongMargin [Lattice D] [GCommSemigroup Φ] extends GMargin Φ where
  margin_trans (φ : Φ x) (y z : D) (p : y ≤ x) (q : z ≤ y) (r : z ≤ x) : StrongMarginTransStatement φ y z p q r
  margin_mul (φ : Φ x) (ψ : Φ y) (p : x ≤ x ⊔ y) (q : x ⊓ y ≤ y) (r : x ⊔ x ⊓ y = x) : StrongMarginMulStatement φ ψ p q r


class GWeakMargin [DistribLattice D] [GCommSemigroup Φ] extends GMargin Φ where
  margin_trans (φ : Φ x) (p : y ≤ x) (q : z ≤ y) : StrongMarginTransStatement φ p q (le_trans q p)
  margin_mul (φ : Φ x) (ψ : Φ y) : StrongMarginMulStatement φ ψ le_sup_left inf_le_right sup_inf_self


def margin [LE D] [GMargin Φ] (φ : ValuationAlgebra Φ) (p : y ≤ ð φ) := mk (GMargin.margin φ.snd y p)


infixl:70 " ⇓ " => margin


class GValuationAlgebra [DistribLattice D] extends GCommSemigroup Φ, GLocalMonoid Φ, GStrongMargin Φ
