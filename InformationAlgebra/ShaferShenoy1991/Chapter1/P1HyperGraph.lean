import Mathlib.Init.Set
import Mathlib.Data.Finset.Basic


/-!
# HyperGraph

This file introduces hypergraphs, branches, and twigs.
-/


namespace HyperGraph


variable
  {X : Type}


/-- Elements of the underlying set of a hypergraph are called "vertices". -/
abbrev Vertex (X : Type) := X


/-- A hyperedge in a hypergraph is any set of vertices. -/
abbrev HyperEdge (X : Type) := Set X


/-- A hypergraph consists of a finite (non-empty) family of subsets of a set. -/
@[ext]
structure HyperGraph (X : Type) where
  val : Finset (HyperEdge X)
  nonempty : Finset.Nonempty val


/-- Drop the proof of nonemptyiness from the data comprising a hypergraph. -/
def HyperGraph.toFinset (ℋ : HyperGraph X) : Finset (HyperEdge X) := ℋ.val


instance : Coe (HyperGraph X) (Finset (HyperEdge X)) := ⟨HyperGraph.toFinset⟩


/-- A hyperedge is a member of a hypergraph when it is so from a `Finset` perspective. -/
protected def mem (a : HyperEdge X) (ℋ : HyperGraph X) : Prop := a ∈ (ℋ : Finset _)


instance : Membership (HyperEdge X) (HyperGraph X) := ⟨HyperGraph.mem⟩


protected def singleton (a : HyperEdge X) : HyperGraph X := ⟨{a}, Finset.singleton_nonempty a⟩


instance : Singleton (HyperEdge X) (HyperGraph X) := ⟨HyperGraph.singleton⟩


/-- A hypergraph is a singleton if and only if it is so as a `Finset`. -/
theorem coe_singleton {ℋ : HyperGraph X} {a : HyperEdge X} : ℋ = {a} ↔ (ℋ : Finset _) = {a} := by
  constructor <;> intro h
  · exact congrArg (HyperGraph.val) h
  · ext : 1
    exact h
  done


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
private def Twig'
    {X}
    (ℋ : HyperGraph X)
    (t : HyperEdge X)
    :
    Prop
    :=
  ∃ b ∈ ℋ, Branch ℋ b t


/-- Utility proposition stipulating that a twig is disjoint from a hypergraph. -/
private def DisjointTwig'
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
  { t : HyperEdge X // Twig' ℋ t }


/-- The type of all disjoint twigs of a hypergraph. -/
def DisjointTwig
    {X}
    (ℋ : HyperGraph X)
    :=
  { t : HyperEdge X // DisjointTwig' ℋ t }


instance {X} {ℋ : HyperGraph X} : CoeOut (DisjointTwig ℋ) (HyperEdge X) where
  coe t := t.val
