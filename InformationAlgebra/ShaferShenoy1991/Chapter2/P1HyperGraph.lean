import Mathlib.Init.Set
import Mathlib.Data.Finset.Basic


/-!
# HyperGraph

This file introduces hypergraphs, branches, and twigs.
-/


namespace HyperGraph


variable
  {X : Type}
  [DecidableEq X]


/-- Elements of the underlying set of a hypergraph are called "vertices". -/
abbrev Vertex (X : Type) := X


/-- A hyperedge in a hypergraph is any set of vertices. -/
abbrev HyperEdge (X : Type) := Finset X


instance : Inter (HyperEdge X) := Finset.instInterFinset


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


protected def insert (a : HyperEdge X) (ℋ : HyperGraph X) : HyperGraph X :=
  ⟨Insert.insert a ℋ, Finset.insert_nonempty a ℋ⟩


instance : Insert (HyperEdge X) (HyperGraph X) := ⟨HyperGraph.insert⟩


/-- A hypergraph is a singleton if and only if it is so as a `Finset`. -/
@[simp]
theorem coe_singleton {ℋ : HyperGraph X} {a : HyperEdge X} : ℋ = {a} ↔ (ℋ : Finset _) = {a} := by
  constructor <;> intro h
  · exact congrArg (HyperGraph.val) h
  · ext : 1
    exact h
  done


@[simp]
theorem mem_singleton {ℋ : HyperGraph X} {a : HyperEdge X} : b ∈ ({a} : HyperGraph X) ↔ b = a := Finset.mem_singleton


section Branches


variable
  {X : Type}
  [DecidableEq X]


/-- In a hypergraph, one edge supports another if the intersection of the latter with
any other *distinct* edge in the hypergraph is contained within the intersection of the former with
that edge.

The emphasis on distinctness is important, because it allows a supported edge to not be a subset
of a supporting edge.

The concept of support in the thoery of local computation is important because valuations factored
over a hypergraph can be reliably marginalized over supported hyperedges (with certain caveats;
see `Twig`), specifically because the supporting edge will "absorb" all the computational content
necessary for computing the factorization of an array marginalized over the supported edge.

Speaking *very* informally, this is because such a factorization requires factoring out all values
of a valuation on vertices "lost" from the graph-- if such vertices were contained by another
hyper-edge, the inductive term in the factorization would have to adjust the valuation on that edge.
In the case that valuations are real-valued, there's flexibility in a factorization over a
hypergraph by scaling factors which intersect up on one side of the intersection and inversely on
the other side. By having a supporting edge, we canisolate all the scaling into the supporting edge
without having to adjust the factor valuations on ANY other edge. Voila, computation localized. -/
def HyperGraph.Supports
    (ℋ : HyperGraph X)
    (a b : HyperEdge X)
    :
    Prop
    :=
  ∀ c ∈ ℋ, c ≠ b → ∀ x ∈ b ∩ c, x ∈ a


/-- Precautionary theorem which highlights that according to the definition, an edge supports itself.

This "degenerate case" complicates discussion down the line, which is why there are extra clauses in
the definition of `Branch`.-/
theorem supports_self (b : HyperEdge X) : HyperGraph.Supports {b} b b := by
  intros a _ _ c h_c_mem
  simp_all only [ne_eq, Finset.mem_inter]
  done


/-- In a hypergraph, one edge is a branch relative to another, distinct edge, if they intersect and
if the former supports the latter.

Requiring that a supporting pair of of edges intersect in this definition eliminates the degenerate
case of two disjoint edges in an otherwise empty hypergraph.

See `HyperGraph.Supports`.-/
def HyperGraph.Branch
    (ℋ : HyperGraph X)
    (b t : HyperEdge X)
    :
    Prop
    :=
  b ≠ t ∧ (b ∩ t).Nonempty ∧ ℋ.Supports b t


/-- In a hypergraph, the property of one edge being a twig relative to another is reciprocal to
that of being a branch.

See `Branch`.-/
def HyperGraph.Twig'
    (ℋ : HyperGraph X)
    (t : HyperEdge X)
    :
    Prop
    :=
  ∃ b ∈ ℋ, ℋ.Branch b t


/-- Utility proposition stipulating that a twig is disjoint from a hypergraph. -/
def HyperGraph.DisjointTwig'
    (ℋ : HyperGraph X)
    (t : HyperEdge X)
    :
    Prop
    :=
  t ∉ ℋ ∧ ℋ.Twig' t


/-- The type of all twigs of a hypergraph. -/
def HyperGraph.Twig
    (ℋ : HyperGraph X)
    :=
  { t : HyperEdge X // Twig' ℋ t }


/-- The type of all disjoint twigs of a hypergraph. -/
def HyperGraph.DisjointTwig
    (ℋ : HyperGraph X)
    :=
  { t : HyperEdge X // ℋ.DisjointTwig' t }


instance {ℋ : HyperGraph X} : CoeOut (ℋ.DisjointTwig) (HyperEdge X) where
  coe t := t.val


namespace List


def toHyperGraph (root : HyperEdge X) (nonRoots : List (HyperEdge X)) : HyperGraph X :=
  ⟨nonRoots.toFinset ∪ {root}, Finset.Nonempty.inr <| Finset.singleton_nonempty root⟩


theorem mem_toHyperGraph
    {root : HyperEdge X}
    {nonRoots : List (HyperEdge X)}
    :
    a ∈ toHyperGraph root nonRoots ↔ a ∈ nonRoots ∨ a = root
    := by
  simp_all only [Membership.mem]
  simp_all only [HyperGraph.mem, HyperGraph.toFinset, toHyperGraph]
  simp_all only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset]
  exact Iff.rfl
  done
