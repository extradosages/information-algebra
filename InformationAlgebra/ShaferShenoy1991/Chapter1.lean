import Mathlib


/-!
# Shenoy, Shafer - 1991 - Local Computation in Hypertrees - Chapter 1

This file establishes some basic definitions

- `HyperGraph X`
- `Branch ℋ b t`
- `Hypertree X`
-/


namespace HyperGraph


variable
  (X : Type*)
  [DecidableEq X]


/-- Elements of the underlying set of a hypergraph are called "vertices". -/
abbrev Vertex := X


/-- A hyperedge in a hypergraph is any set of vertices. -/
abbrev HyperEdge := Set X


/-- A hypergraph consists of a finite (non-empty) family of subsets of a set. -/
structure HyperGraph (X) where
  val : Finset (HyperEdge X)
  nonempty : val.Nonempty


/-- Drop the proof of nonemptyiness from the data comprising a hypergraph. -/
def HyperGraph.toFinset (ℋ : HyperGraph X) : Finset (HyperEdge X) := ℋ.val


instance : Coe (HyperGraph X) (Finset (HyperEdge X)) where
  coe ℋ := ℋ.toFinset


/-- A hyperedge is a member of a hypergraph when it is so from a `Finset` perspective. -/
def HyperGraph.mem {X} (a : HyperEdge X) (ℋ : HyperGraph X) : Prop := a ∈ (ℋ : Finset _)


instance : Membership (HyperEdge X) (HyperGraph X) where
  mem a ℋ := HyperGraph.mem a ℋ


instance : Singleton (HyperEdge X) (HyperGraph X) where
  singleton b := ⟨{b}, Finset.singleton_nonempty b⟩


/-- In a hypergraph, one edge dominates another if the intersection of the latter with
any other *distinct* edge in the hypergraph is contained within the intersection of the former with
that edge.

The emphasis on distinctness is important, because it allows a dominated edge to not be a subset
of a dominating edge. -/
protected def Dominates
    {X}
    (ℋ : HyperGraph X)
    (a : HyperEdge X)
    (b : HyperEdge X)
    :
    Prop
    :=
  ∀ c ∈ ℋ, c ≠ b → ∀ x ∈ b ∩ c, x ∈ a


/-- Precautionary theorem which highlights that according to the definition, an edge dominates itself. -/
theorem dominates_self (b : HyperEdge X) : HyperGraph.Dominates {b} b b := by
  intros a _ _ c h_c_mem
  exact Set.mem_of_mem_inter_left h_c_mem
  done


/-- In a hypergraph, one edge is a branch relative to another, distinct edge, if they intersect and
if the former dominates the latter.

Requiring that a dominating pair of of edges intersect in this definition eliminates the degenerate
case of two disjoint edges in an otherwise empty hypergraph.

See `HyperGraph.Dominates`.-/
def Branch
    {X}
    (ℋ : HyperGraph X)
    (b : HyperEdge X)
    (t : HyperEdge X)
    :
    Prop
    :=
  b ≠ t ∧ b ∩ t ≠ ∅ ∧ HyperGraph.Dominates ℋ b t


/-- In a hypergraph, the property of one edge being a twig relative to another is reciprocal to
that of being a branch.

See `Branch`.-/
protected def Twig'
    {X}
    (ℋ : HyperGraph X)
    (t : HyperEdge X)
    :
    Prop
    :=
  ∃ b ∈ ℋ, Branch ℋ b t


/-- Utility proposition stipulating that a twig is disjoint from a hypergraph. -/
protected def DisjointTwig'
    {X}
    (ℋ : HyperGraph X)
    (t : HyperEdge X)
    :
    Prop
    :=
  t ∉ ℋ ∧ HyperGraph.Twig' ℋ t


/-- The type of all twigs of a hypergraph. -/
def Twig
    {X}
    (ℋ : HyperGraph X)
    :=
  { t : HyperEdge X // HyperGraph.Twig' ℋ t }


/-- The type of all disjoint twigs of a hypergraph. -/
def DisjointTwig
    {X}
    (ℋ : HyperGraph X)
    :=
  { t : HyperEdge X // HyperGraph.DisjointTwig' ℋ t }


instance {X} {ℋ : HyperGraph X} : CoeOut (DisjointTwig ℋ) (HyperEdge X) where
  coe t := t.val


private inductive HyperTree' X where
  | nil (r : HyperEdge X) : HyperTree' X
  | cons (ℋ : HyperGraph X) (t : DisjointTwig ℋ) : HyperTree' X


/-- A hypertree is an ordering of the edges in a hypergraph such that each edge is
a twig for the graph comprised of the section of edges preceding it in the ordering. -/
def HyperTree := HyperTree'


/-- Obtain a hypergraph from a hypertree. -/
def HyperTree.toHyperGraph (𝒯 : HyperTree X) : HyperGraph X :=
  match 𝒯 with
    | HyperTree'.nil r => ⟨{r}, Finset.singleton_nonempty r⟩
    | HyperTree'.cons ℋ t => ⟨Finset.cons t.1 ℋ.1 t.2.left, Finset.nonempty_cons t.2.left⟩


instance : Coe (HyperTree X) (HyperGraph X) where
  coe 𝒯 := 𝒯.toHyperGraph


/-- A trivial hypertree. -/
def HyperTree.nil {X} := @HyperTree'.nil X


notation:70 "[" r "]ₜ" => HyperTree.nil r


/-- Attach a twig onto a hypertree to produce a new hypertree. -/
def HyperTree.cons {X} (𝒯 : HyperTree X) (t : @DisjointTwig X 𝒯) := HyperTree'.cons 𝒯 t


infixr:70 " ::ₜ " => HyperTree.cons


instance : Singleton (HyperEdge X) (HyperTree X) where
  singleton r := [r]ₜ


/-- An inductive API for proposing membership of an edge in a hypertree. -/
def HyperTree.inductiveMem {X} (a : HyperEdge X) (𝒯 : HyperTree X) : Prop :=
  match 𝒯 with
    | HyperGraph.HyperTree'.nil b => a = b
    | HyperGraph.HyperTree'.cons 𝒯' b => a = b ∨ a ∈ 𝒯'


instance : Membership (HyperEdge X) (HyperTree X) where
  mem a 𝒯 := HyperTree.inductiveMem a 𝒯


/-- A "proxy" API for proposing membership of an edge in a hypertree, appealing to the tree's
`Finset` API derived from -/
def HyperTree.proxyMem {X} (a : HyperEdge X) (𝒯 : HyperTree X) : Prop := a ∈ (𝒯 : HyperGraph X)


/-- The inductive and proxy membership APIs are equivalent. -/
theorem HyperTree.inductive_mem_iff_proxy_mem
    (a : HyperEdge X)
    (𝒯 : HyperTree X)
    :
    HyperTree.inductiveMem a 𝒯 ↔ HyperTree.proxyMem a 𝒯
    := by
  apply Iff.intro <;> (intro h_mem₁; cases 𝒯)
  case mp.nil =>
    rw [h_mem₁]
    exact List.Mem.head []
  case mp.cons =>
    apply Multiset.mem_cons.mpr
    exact h_mem₁
  case mpr.nil =>
    cases h_mem₁
    case head => rfl
    case tail =>
      rename_i h_mem₂
      -- Weird
      cases h_mem₂
  case mpr.cons =>
    apply Multiset.mem_cons.mp
    exact h_mem₁
  done



structure HyperTree (X) where
  hyperGraph : HyperGraph X
  construction : HyperTree X
  coe : construction.toHyperGraph = hyperGraph



-- theorem eq_singleton_iff_unique_mem {s : HyperTree X} {a : HyperEdge X} : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a := by
--   constructor <;> intro t
--   · rw [t]
--     exact ⟨Finset.mem_singleton_self _, fun _ => Finset.mem_singleton.1⟩
--   · ext
--     rw [Finset.mem_singleton]
--     exact ⟨t.right _, fun r => r.symm ▸ t.left⟩


-- theorem singleton_iff_unique_mem (s : Finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s := by
--   simp only [eq_singleton_iff_unique_mem, ExistsUnique]


theorem two_elt_hypertree_lemma (𝒯 : HyperTree X) (p : 𝒯 = ([a₁]ₜ) ::ₜ a₂) : a₁ ∩ a₂ ≠ ∅ := by
  sorry
  done
