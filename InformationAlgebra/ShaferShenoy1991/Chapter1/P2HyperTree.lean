import InformationAlgebra.ShaferShenoy1991.Chapter1.P1HyperGraph


/-!
# HyperTree

This file introduces hypertrees.
-/

open HyperGraph


namespace HyperTree


variable
  {X : Type}


private inductive HyperTree' (X : Type) where
  | nil (a : HyperEdge X) : HyperTree' X
  | cons (ℋ : HyperGraph X) (t : DisjointTwig ℋ) : HyperTree' X



/-- A hypertree is an ordering of the edges in a hypergraph such that each edge is
a twig for the graph comprised of the section of edges preceding it in the ordering. -/
abbrev HyperTree := HyperTree'


variable
  (𝒯 : HyperTree X)


/-- Obtain a hypergraph from a hypertree. -/
def HyperTree.toHyperGraph : HyperGraph X :=
  match 𝒯 with
    | HyperTree'.nil a => ⟨{a}, Finset.singleton_nonempty a⟩
    | HyperTree'.cons ℋ a => ⟨Finset.cons a.1 ℋ a.2.left, Finset.nonempty_cons a.2.left⟩


instance : Coe (HyperTree X) (HyperGraph X) where
  coe 𝒯 := 𝒯.toHyperGraph


/-- A trivial hypertree. -/
def HyperTree.nil := @HyperTree'.nil X


notation:70 "[" a "]ₜ" => HyperTree.nil a


/-- Attach a twig onto a hypertree to produce a new hypertree. -/
def HyperTree.cons (t : @DisjointTwig X 𝒯) := HyperTree'.cons 𝒯 t


infixr:70 " ::ₜ " => HyperTree.cons


instance : Singleton (HyperEdge X) (HyperTree X) where
  singleton a := [a]ₜ


/-- A singleton hypertree re-interpreted as a hypergraph is equal to the singleton hypergraph. -/
theorem coe_singleton (a : HyperEdge X) : HyperTree.toHyperGraph {a} = {a} := by
  constructor
  done


/-- An inductive API for proposing membership of an edge in a hypertree. -/
def inductiveMem {X} (a : HyperEdge X) (𝒯 : HyperTree X) : Prop :=
  match 𝒯 with
    | HyperTree'.nil b => a = b
    | HyperTree'.cons ℋ b => a = b ∨ a ∈ ℋ


instance : Membership (HyperEdge X) (HyperTree X) where
  mem a 𝒯 := inductiveMem a 𝒯


/-- A "proxy" API for proposing membership of an edge in a hypertree, appealing to the tree's
`Finset` API derived from -/
def proxyMem {X} (a : HyperEdge X) (𝒯 : HyperTree X) : Prop := a ∈ (𝒯 : HyperGraph X)


/-- The inductive and proxy membership APIs are equivalent. -/
theorem coe_mem
    {a : HyperEdge X}
    {𝒯 : HyperTree X}
    :
    inductiveMem a 𝒯 ↔ proxyMem a 𝒯
    := by
  constructor <;> (intro h_mem₁; cases 𝒯)
  · rw [h_mem₁]
    exact List.Mem.head []
  · apply Multiset.mem_cons.mpr
    exact h_mem₁
  · cases h_mem₁
    case head => rfl
    case tail =>
      rename_i h_mem₂
      -- Weird
      cases h_mem₂
  · apply Multiset.mem_cons.mp
    exact h_mem₁
  done


@[simp]
theorem mem_head {𝒯 : HyperTree X} {t : DisjointTwig 𝒯} : (t : HyperEdge X) ∈ 𝒯 ::ₜ t := by
  apply Or.inl rfl
  done

@[simp]
theorem mem_tail' {x : HyperEdge X} {ℋ : HyperGraph X} {t : DisjointTwig ℋ} (p : x ∈ ℋ) : x ∈ HyperTree'.cons ℋ t := by
  apply Or.inr p
  done


@[simp]
theorem mem_singleton_self (a : HyperEdge X) : a ∈ ({a} : HyperTree X) := by
  rfl
  done


@[simp]
theorem mem_singleton {a b : HyperEdge X} : a ∈ ({b} : HyperTree X) ↔ a = b := by
  constructor <;> intro h_mem
  · exact h_mem
  · rw [h_mem]
    exact HyperTree.mem_singleton_self _
  done


-- Long proof, not very useful. Good exercise.
 theorem eq_singleton_iff_unique_mem {𝒯 : HyperTree X} {a : HyperEdge X} : 𝒯 = {a} ↔ a ∈ 𝒯 ∧ ∀ x ∈ 𝒯, x = a := by
  constructor <;> intro h_mem
  · rw [h_mem]
    exact ⟨HyperTree.mem_singleton_self _, fun _ => HyperTree.mem_singleton.1⟩
  · cases 𝒯 <;> cases h_mem
    · rename_i h_mem_right h_mem_left
      rw [h_mem_right]
      rfl
    · rename_i ℋ t h_mem_left h_mem_right
      have h_t_nin_H : ↑t ∉ ℋ := t.2.1
      have h_t_in_H : ↑t ∈ ℋ := by
        have h_H_singleton : ℋ = ⟨{↑t}, _⟩ := by
          apply HyperGraph.coe_singleton.mpr
          apply (@Finset.eq_singleton_iff_nonempty_unique_mem (HyperEdge X) ℋ (↑t)).mpr
          have h_t_unique_mem_H : ∀ x ∈ ℋ, x = t := by
            intro x h_x_in_H
            simp only [h_x_in_H, h_mem_right, mem_tail']
            have h_t_eq_a : t = a := by
              apply h_mem_right
              dsimp [Membership.mem, inductiveMem]
              apply Or.inl rfl
              done
            rw [h_t_eq_a]
            done
          exact ⟨ℋ.nonempty, h_t_unique_mem_H⟩
        have h_t_in_H_val : ↑t ∈ ℋ.val := by
          rw [congrArg HyperGraph.val h_H_singleton]
          apply Finset.mem_singleton_self
        exact h_t_in_H_val
      contradiction


 theorem singleton_iff_unique_mem (𝒯 : HyperTree X) : (∃ a, 𝒯 = {a}) ↔ ∃! a, a ∈ 𝒯 := by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]


theorem two_elt_hypertree_lemma (𝒯 : HyperTree X) (p : 𝒯 = ([a₁]ₜ) ::ₜ a₂) : a₁ ∩ a₂ ≠ ∅ := by
  sorry
  done
