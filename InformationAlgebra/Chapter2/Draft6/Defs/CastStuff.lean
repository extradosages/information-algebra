


section CastValuationAlgebra

open CastValuationAlgebra

variable
  [DistribLattice D]
  {Φ : D → Type*}
  [CastValuationAlgebra Φ]
  {x y : D}
  (φ : Φ x)
  (ψ : Φ y)

@[simp]
theorem cast_symm (p : x = y) : (p↾ φ) = ψ ↔ φ = ((Eq.symm p)↾ ψ) := by
  cases p
  rw [cast_refl, cast_refl]
  done

@[simp]
theorem cast_symm_cast_left {φ : Φ x} {ψ : Φ y} {p : x = y} (q : (p↾ φ) = ψ) : φ = ((Eq.symm p)↾ ψ) := (ValuationAlgebra.cast_symm φ ψ p).mp q

@[simp]
theorem cast_symm_cast_right {φ : Φ x} {ψ : Φ y} {p : y = x}  (q : φ = (p↾ ψ)) : ((Eq.symm p)↾ φ) = ψ := (ValuationAlgebra.cast_symm φ ψ (Eq.symm p)).mpr q

/-- Casting across two equalities is casting across their transitivity -/
theorem cast_trans (φ : Φ x) (p : x = y) (q : y = z) : q↾ (p↾ φ) = (Eq.trans p q)↾ φ := by
  cases p
  cases q
  rw [cast_refl, cast_refl]
  done

@[simp]
theorem cast_mul_left (φ : Φ x) (ψ : Φ y) (p : x = z) : (p↾ φ) ⊗ ψ = (congrArg (· ⊔ y) p)↾ (φ ⊗ ψ) := by
  cases p
  rw [cast_refl, cast_refl]
  done

@[simp]
theorem cast_mul_right (φ : Φ x) (ψ : Φ y) (p : y = z) : φ ⊗ (p↾ ψ) = (congrArg (x ⊔ ·) p)↾ (φ ⊗ ψ) := by
  cases p
  rw [cast_refl, cast_refl]
  done

@[simp]
theorem cast_margin_le_of_eq (φ : Φ x) (y z : D) (p : y ≤ x) (q : z = x) : (φ ⇓ y, p) = ((q.symm↾ φ) ⇓ y, le_of_le_of_eq p q.symm) := by
  cases q
  rw [cast_refl]
  done

@[simp]
theorem cast_margin_eq_of_le (φ : Φ x) (y z : D) (p : y ≤ x) (q : z = y) : (φ ⇓ y, p) = q↾ (φ ⇓ z, le_of_eq_of_le q p) := by
  cases q
  rw [cast_refl]
  done

@[simp]
theorem mul_assoc_cast_right (φ : Φ x) (ψ : Φ y) (ϕ : Φ z) : ((φ ⊗ ψ) ⊗ ϕ) = sup_assoc.symm↾ (φ ⊗ (ψ ⊗ ϕ)) := mul_assoc φ ψ ϕ

@[simp]
theorem mul_assoc_cast_left (φ : Φ x) (ψ : Φ y) (ϕ : Φ z) : sup_assoc↾ ((φ ⊗ ψ) ⊗ ϕ) = (φ ⊗ (ψ ⊗ ϕ)) := cast_symm_cast_right <| mul_assoc φ ψ ϕ

@[simp]
theorem mul_one_cast_right (φ : Φ x) : φ = sup_idem↾ (φ ⊗ e x) := mul_one φ

@[simp]
theorem mul_one_cast_left (φ : Φ x) : sup_idem.symm↾ φ = φ ⊗ e x := cast_symm_cast_right <| mul_one φ

@[simp]
theorem margin_mul_cast_right (φ : Φ x) (ψ : Φ y) : (φ ⊗ ψ ⇓ x, le_sup_left) = sup_inf_self↾ (φ ⊗ (ψ ⇓ x ⊓ y, inf_le_right)) := margin_mul φ ψ

@[simp]
theorem margin_mul_cast_left (φ : Φ x) (ψ : Φ y) : sup_inf_self.symm↾ (φ ⊗ ψ ⇓ x, le_sup_left) = φ ⊗ (ψ ⇓ x ⊓ y, inf_le_right) := cast_symm_cast_right <| margin_mul φ ψ

end CastValuationAlgebra

variable
  [Lattice D]

def StrongMarginReflStatement {Φ : D → Type*} [GMargin Φ]  (φ : Φ x) (p : x ≤ x) := φ = (φ ⇓ x, p)
def StrongMarginTransStatement {Φ : D → Type*} [GMargin Φ] (φ : Φ x) (p : z ≤ y) (q : y ≤ x) (r : z ≤ x) := (φ ⇓ z, r) = ((φ ⇓ y, q) ⇓ z, p)
def StrongMarginMulStatement {Φ : D → Type*} [GMargin Φ] [GMul Φ] (φ : Φ x) (ψ : Φ y) (p : x ≤ x ⊔ y) (q : x ⊓ y ≤ y) (r : x ≤ x ⊔ x ⊓ y) := (φ ⊗ ψ ⇓ x, p) = (φ ⊗ (ψ ⇓ x ⊓ y, q) ⇓ x, r)
def StrongMulOneStatement {Φ : D → Type*} [GMargin Φ] [GMul Φ] [GOne Φ] (φ : Φ x) (p : x ≤ x ⊔ x) := φ = ((φ ⊗ e x) ⇓ x, p)
def MulCommStatement {Φ : D → Type*} [GMaring Φ] [GMul Φ] (φ : Φ x) (ψ : Φ y) (p : )
def WeakMarginReflStatement {Φ : D → Type*} [GMargin Φ] (φ : Φ x) := StrongMarginReflStatement φ (le_refl x)
def WeakMarginTransStatement {Φ : D → Type*} [GMargin Φ] (φ : Φ x) (p : z ≤ y) (q : y ≤ x)  := StrongMarginTransStatement φ p q (le_trans p q)
def WeakMarginMulStatement {Φ : D → Type*} [GMargin Φ] [GMul Φ] (φ : Φ x) (ψ : Φ y) := StrongMarginMulStatement φ ψ le_sup_left inf_le_right le_sup_left
def WeakMulOneStatement {Φ : D → Type*} [GMargin Φ] [GMul Φ] [GOne Φ] (φ : Φ x) := StrongMulOneStatement φ le_sup_left

class ValuationAlgebra extends GMul Φ, GOne Φ, GMargin Φ where
  /-- Marginalization by a valuation's grade is the identity -/
  margin_refl (φ : Φ x) (p : x ≤ x) : StrongMarginReflStatement φ p
  /-- Marginalization respects transitivity of sub-grades -/
  margin_trans (φ : Φ x) (p : z ≤ y) (q : y ≤ x) (r : z ≤ x) : StrongMarginTransStatement φ p q r
  /-- Marginalization distributes across multiplication in a particular way -/
  margin_mul (φ : Φ x) (ψ : Φ y) (p : x ≤ x ⊔ y) (q : x ⊓ y ≤ y) (r : x ≤ x ⊔ x ⊓ y) : StrongMarginMulStatement φ ψ p q r
  /-- Intra-grade multiplication by the grade's `one` is the identity -/
  mul_one (φ : Φ x) (p : x ≤ x ⊔ x) : StrongMulOneStatement φ p
  /-- Inter-grade multiplication is commutative -/
  mul_comm (φ : Φ x) (ψ : Φ y) : φ ⊗ ψ = sup_comm↾ (ψ ⊗ φ)
  /-- Inter-grade multiplication is associative -/
  mul_assoc (φ : Φ x) (ψ : Φ y) (ϕ : Φ z) (p : x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z) : (φ ⊗ ψ) ⊗ ϕ = ((φ ⊗ (ψ ⊗ ϕ)) ⇓ (x ⊓ y) ⊓ z,
  /-- Inter-grade multiplication of `one` elements produces a `one` element -/
  mul_one_one : (e x : Φ x) ⊗ (e y) = (e x ⊔ y)



section ValuationAlgebra
