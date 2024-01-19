import Mathlib


/-!
# Shenoy, Shafer - 1991 - Local Computation in Hypertrees - Chapter 1

This file establishes some basic definitions

- `HyperGraph X`
- `Branch ℋ b t` and `Twig ℋ t b`
- `Hypertree ℋ`
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


/-- Attach a twig onto a hypertree to produce a new hypertree. -/
def HyperTree.cons {X} (ℋ : HyperTree X) (t : @DisjointTwig X ℋ) := HyperGraph.HyperTree'.cons ℋ t
