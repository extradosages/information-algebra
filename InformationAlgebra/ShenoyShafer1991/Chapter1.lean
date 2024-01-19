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
abbrev HyperGraph := { ℋ : Finset (HyperEdge X) // ℋ.Nonempty }


instance : Membership (HyperEdge X) (HyperGraph X) where
  mem b ℋ := b ∈ ℋ.val


/-- In a hypergraph, one edge dominates another if the intersection of the latter with
any other *distinct* edge in the hypergraph is contained within the intersection of the former with
that edge.

The emphasis on distinctness is important, because it allows a dominated edge to not be a subset
of a dominating edge. -/
protected def Dominates
    {X}
    (ℋ : HyperGraph X)
    (b : HyperEdge X)
    (t : HyperEdge X)
    :
    Prop
    :=
  ∀ h ∈ ℋ, h ≠ t → ∀ x ∈ t ∩ h, x ∈ b


/-- In a hypergraph, one edge is a branch relative to another if they intersect and if the
former dominates the latter.

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
  b ∩ t ≠ ∅ ∧ HyperGraph.Dominates ℋ b t


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


protected inductive HyperTree' X where
  | nil (r : HyperEdge X) : HyperGraph.HyperTree' X
  | cons (ℋ : HyperGraph X) (t : DisjointTwig ℋ) : HyperGraph.HyperTree' X


/-- A hypertree is a hypergraph that can be constructed step-by-step by adding twigs. -/
def HyperTree := HyperGraph.HyperTree'


/-- Any hypertree is also a hypergraph. -/
instance {X} : Coe (HyperTree X) (HyperGraph X) where
  coe 𝒯 := match 𝒯 with
    | HyperGraph.HyperTree'.nil r => ⟨{r}, Finset.singleton_nonempty r⟩
    | HyperGraph.HyperTree'.cons ℋ t => ⟨Finset.cons t.1 ℋ.1 t.2.left, Finset.nonempty_cons t.2.left⟩


/-- Any hypergraph consisting of a lone hyperedge is a hypertree. -/
def HyperTree.nil {X} := @HyperGraph.HyperTree'.nil X


notation:70 "[" r "]ₜ" => HyperTree.nil r


/-- Attach a twig onto a hypertree to produce a new hypertree. -/
def HyperTree.cons {X} (ℋ : HyperTree X) (t : @DisjointTwig X ℋ) := HyperGraph.HyperTree'.cons ℋ t


infixr:70 " ::ₜ " => HyperTree.cons


def HyperTreeForGraph (ℋ : HyperGraph X) := { 𝒯 : HyperTree X // (𝒯 : HyperGraph X) = ℋ }


instance : Singleton (HyperEdge X) (HyperTree X) where
  singleton r := [r]ₜ


instance : Membership (HyperEdge X) (HyperTree X) where
  mem a 𝒯 := match 𝒯 with
    | HyperGraph.HyperTree'.nil b => a = b
    | HyperGraph.HyperTree'.cons 𝒯' b => a = b ∨ a ∈ 𝒯'


theorem mem_tree_iff_mem_graph (a : HyperEdge X) (𝒯 : HyperTree X) : a ∈ 𝒯 ↔ a ∈ (𝒯 : HyperGraph X) := by
  sorry
  done


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
