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
ANY other edge in the hypergraph is contained within the intersection of the former with that
edge. -/
protected def Dominating
    {X}
    (ℋ : HyperGraph X)
    (b : HyperEdge X)
    (t : HyperEdge X)
    :
    Prop
    :=
  ∀ h ∈ ℋ, h ≠ t → ∀ x ∈ t, x ∈ h → x ∈ b


/-- In a hypergraph, one edge is a branch relative to another if they intersect and if the
former dominates the latter.

See `HyperGraph.Dominating`.-/
def Branch
    {X}
    (ℋ : HyperGraph X)
    (b : HyperEdge X)
    (t : HyperEdge X)
    :
    Prop
    :=
  HyperGraph.Intersecting b t ∧ HyperGraph.Dominating ℋ b t


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


/-- `HyperTree t ℋ p` means that `t` is a twig for the hypertree `ℋ` and is not already a hyperedge
in `ℋ` (via `p`).-/
inductive HyperTree : (t : HyperEdge X) → (ℋ : HyperGraph X) → (p : t ∉ ℋ) → Prop
  | nil {root : HyperEdge X} : HyperTree root ∅ _
  | cons : ∀ {a b : HyperEdge X} {ℋ : HyperGraph X}, Twig ℋ a b → HyperTree b ℋ q → HyperTree a (Set.insert b ℋ) p
