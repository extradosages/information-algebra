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


/-- Elements of the underlying set of a hypergraph are called "vertices". -/
abbrev Vertex := X


/-- A hyperedge in a hypergraph is any set of vertices. -/
abbrev HyperEdge := Set X


/-- A hypergraph consists of a (non-empty) family of subsets of a set. -/
abbrev HyperGraph := Set (HyperEdge X)


protected def Intersecting {X} (b : HyperEdge X) (t : HyperEdge X) := b ∩ t ≠ ∅


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
  HyperGraph.Intersecting b t ∧ HyperGraph.Dominates ℋ b t


/-- In a hypergraph, the property of one edge being a twig relative to another is reciprocal to
that of being a branch.

See `Branch`.-/
def Twig
    {X}
    (ℋ : HyperGraph X)
    (t : HyperEdge X)
    (b : HyperEdge X)
    :
    Prop
    :=
  Branch ℋ b t


def Twig'
    {X}
    (ℋ : HyperGraph X)
    (t : HyperEdge X)
    :
    Prop
    :=
  ∃ b ∈ ℋ, Twig ℋ t b


/-- `HyperTree t ℋ p` means that `t` is a twig for the hypertree `ℋ` and is not already a hyperedge
in `ℋ` (via `p`).-/
inductive HyperTree : (t : HyperEdge X) → (ℋ : HyperGraph X) → Prop
  | nil {root : HyperEdge X} : HyperTree root ∅
  | cons : ∀ {a : HyperEdge X} {ℋ : HyperGraph X}, Twig' ℋ a → HyperTree a ℋ
