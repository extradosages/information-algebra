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


protected theorem hyper_tree_root X : ∀ _ : HyperEdge X, True := by
  exact fun _ ↦ trivial
  done


protected def HyperTree' : (ℋ : HyperGraph X) → (Finset.Nonempty ℋ.val) → Prop :=
  fun ⟨s, h⟩ _ ↦
    if ∃ a : HyperEdge X, s = {a} then
      True
    else if ∃ (a : HyperEdge X) (hh : a ∉ s), s = (Finset.cons a s hh) then
      HyperGraph.DisjointTwig' ⟨s, h⟩ a
    else
      False


/-
⊢ ∀ {α : Type u_4} {p : (s : Finset α) → Finset.Nonempty s → Prop},
  (∀ (a : α), p {a} _) →
    (∀ ⦃a : α⦄ (s : Finset α) (h : a ∉ s) (hs : Finset.Nonempty s), p s hs → p (Finset.cons a s h) _) →
      ∀ {s : Finset α} (hs : Finset.Nonempty s), p s hs

-/
/- To prove a proposition about a nonempty `s : Finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : Finset α`, then it also holds for the `Finset`
obtained by inserting an element in `t`. -/
#check @Finset.Nonempty.cons_induction (HyperEdge X)


def HyperTree (ℋ : HyperGraph X) : Prop :=
  Finset.Nonempty.cons_induction (HyperGraph.hyper_tree_root X)


#check Acc
#check Finset.cons

def HyperTree (ℋ : HyperGraph X) : Prop :=
  if ℋ = 0 then
    False
  else if ∃ x, ℋ = {x} then
    True
  else
