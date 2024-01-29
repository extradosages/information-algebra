import InformationAlgebra.ShaferShenoy1991.Chapter2.P1HyperGraph


/-!
# HyperTree

This file introduces hypertrees.


## Implementation History

The `HyperTree` type was originally implemented as an inductive type, in which terms were
constructed sequentially by adding disjoint twigs. This was extremely cumbersome, because of
how thick the disjoint twig type is.

The API that I really wanted (for small explicit constructions) was to be able to just list
out the edges in the construction sequence and then have a space where subgoals were created
for the list asking me to verify each of the individual branchings that pin together a such a
hypertree. This was totally infeasible in the literal, low-level inductive model.

The objective in that case suggests an obvious solution: model hypertrees as lists of edges.
Fortunately, the `List` namespace is very, very rich. Making the switch made a whole lot of
proofs much, much easier. The only thing which was just a bit tricky was coming up with the
inductive proposition that each edge added to a tree is a twig for its section, but the difficulty
was entirely a consequence of unfamiliarity with inductive propositions at the time, and was
easily overcome.
-/

open HyperGraph


namespace HyperTree


variable
  {X : Type}
  [inst : DecidableEq X]


/-- The type of all proofs that a nonempty list of hyperedges can be decomposed into the sequential
addition of twigs.

The nonemptiness of a list is encoded in the first argument to the type; this is an edge which is
guaranteed to be present in the list, called the "root". Although it doesn't seriously impact the
semantics of this type, we are operating under the assumption that the (latent) isomorphism between
this type of pairs and the type of lists with a proof of their non-emptiness assumes that the "root"
is mapped to last element of the nonempty list.

Note that this type does not require that a twig involved in the construction sequence is disjoint
at each step. Although this is essential in the definition of a `HyperTree`, it has been excluded
from this type for accessibility reasons. That constraint is instead folded into the `HyperTree`
type itself, as a separate `List.Nodup` proof. -/
inductive ConsTwig : (HyperEdge X) → (List (HyperEdge X)) → Prop where
  /-- Any trivial hypergraph is a vacuously a hypertree.

  Note that a trivial hypergraph has one edge. -/
  | nil  : ∀ {root : HyperEdge X}, ConsTwig root []
  /-- By providing a proof that an edge `a` is a twig for the hypergraph comprised of the elements
  of a nonempty list `b::l` and a proof that `b::l` is itself constructed of twigs, we obtain a
  proof that the `a::b::l` is itself constructed by twigs. -/
  | cons : ∀ {edge root : HyperEdge X} {nonRoots : List (HyperEdge X)}, (HyperGraph.Twig' (List.toHyperGraph root nonRoots) edge) → (ConsTwig root nonRoots) → ConsTwig root (edge :: nonRoots)

attribute [simp] ConsTwig.nil
attribute [simp] ConsTwig.cons


/-- A `HyperTree` is a `HyperGraph`, together with an ordering of its edges such that each edge is
a twig for the hypergraph given by its downward section in the ordering.
-/
structure HyperTree (X : Type) [inst : DecidableEq X] where
  /-- The root of the hypertree. -/
  root : HyperEdge X
  /-- Non-root edges in the hypertree.

  Provided in *descending* order in the construction sequence.-/
  nonRoots : List (HyperEdge X)
  /-- No edges in a hypertree are repeated. -/
  nodup : nonRoots.Nodup ∧ root ∉ nonRoots
  /-- The hypertree is constructed by twigs. -/
  cons_twig : @ConsTwig X inst root nonRoots


def HyperTree.toList (𝒯 : HyperTree X) := 𝒯.nonRoots ++ [𝒯.root]


theorem toList_nonempty {𝒯 : HyperTree X} : 𝒯.toList ≠ [] := by
  intro h
  rewrite [HyperTree.toList, List.append_eq_nil] at h
  injection h.right
  done


def HyperTree.toHyperGraph (𝒯 : HyperTree X) : HyperGraph X := List.toHyperGraph 𝒯.root 𝒯.nonRoots


instance : Coe (HyperTree X) (HyperGraph X) := ⟨HyperTree.toHyperGraph⟩


instance : Singleton (HyperEdge X) (HyperTree X) where
  singleton a := ⟨a, [], ⟨List.nodup_nil, List.not_mem_nil a⟩, ConsTwig.nil⟩


theorem coe_singleton {a : HyperEdge X} :  ({a} : HyperTree X) = ({a} : HyperGraph X) := rfl


theorem root_singleton {a : HyperEdge X} : ({a} : HyperTree X).root = a := rfl


instance : Membership (HyperEdge X) (HyperTree X) where
  mem a 𝒯 := a ∈ 𝒯.nonRoots ∨ a = 𝒯.root


theorem mem_singleton {a b : HyperEdge X} : a ∈ ({b} : HyperTree X) ↔ a = b := by
  dsimp only [Membership.mem, singleton]
  constructor <;> intro h₁
  · apply Or.elim h₁
    · intro h₂
      exact absurd (h₂) (List.not_mem_nil a)
    · exact id
  · exact Or.inr h₁
  done


-- TODO: This could probably be smaller
theorem coe_mem {a : HyperEdge X} {𝒯 : HyperTree X} : a ∈ 𝒯 ↔ a ∈ (𝒯 : HyperGraph X) := by
  simp only [Membership.mem]
  simp only [HyperGraph.mem, HyperGraph.toFinset, HyperTree.toHyperGraph, List.toHyperGraph, List.mem_toFinset, List.mem_cons]
  simp only [Membership.mem]
  rw [Or.comm]
  sorry
  done


theorem disjoint_edge_ne_head (𝒯 : HyperTree X) (a : HyperEdge X) (h : a ∉ 𝒯) : a ≠ 𝒯.root :=
  fun h₂ ↦ absurd (h₂) (not_or.mp h |>.right)


theorem disjoint_edge_nin_tail (𝒯 : HyperTree X) (a : HyperEdge X) (h : a ∉ 𝒯) : a ∉ 𝒯.nonRoots := not_or.mp h |>.left


theorem cons_nonRoots_nodup (𝒯 : HyperTree X) (a : HyperEdge X) (h : a ∉ 𝒯) : (a :: 𝒯.nonRoots).Nodup := by
  simp_all only [List.nodup_cons, Membership.mem, HyperTree.toList]
  rw [not_or] at h
  exact ⟨h.left, 𝒯.nodup.left⟩
  done


theorem cons_root_ne (𝒯 : HyperTree X) (a : HyperEdge X) (h : a ∉ 𝒯) : 𝒯.root ∉ (a :: 𝒯.nonRoots) := by
  intro h₂
  simp_all only [List.mem_cons]
  apply Or.elim h₂ <;> intro h₃
  · exact absurd (h₃) (not_or.mp h |>.right |> ne_comm.mp)
  · exact absurd (h₃) 𝒯.nodup.right
  done


def cons_nodup (𝒯 : HyperTree X) (a : HyperEdge X) (h : a ∉ 𝒯) := And.intro (cons_nonRoots_nodup 𝒯 a h) (cons_root_ne 𝒯 a h)


theorem cons_cons_twig (𝒯 : HyperTree X) (a : @HyperGraph.DisjointTwig X inst 𝒯) : ConsTwig 𝒯.root (a :: 𝒯.nonRoots) :=
  ConsTwig.cons a.property.right 𝒯.cons_twig


def HyperTree.nil (a : HyperEdge X) : HyperTree X := {a}


-- TODO: Figure out why `HyperGraph.DisjointTwig` needs so much help.
/-- Attach a new twig to a hypertree, producing another hypertree. -/
def HyperTree.cons (𝒯 : HyperTree X) (a : @HyperGraph.DisjointTwig X inst 𝒯) : HyperTree X := ⟨
    𝒯.root,
    (a :: 𝒯.nonRoots),
    cons_nodup 𝒯 a (Iff.not coe_mem |>.mpr a.property.left),
    cons_cons_twig 𝒯 a
  ⟩


@[inherit_doc]
infixl:70 " ::ₜ "  => HyperTree.cons


theorem mem_cons {𝒯 : HyperTree X} {a : @HyperGraph.DisjointTwig X inst 𝒯} {b : HyperEdge X} : b ∈ (𝒯 ::ₜ a) ↔ b ∈ 𝒯 ∨ b = a := by
  simp only [HyperTree.cons, List.mem_cons, Membership.mem]
  conv =>
    rhs
    rw [or_comm, ←or_assoc]
  apply Iff.or
  · exact List.mem_cons
  · exact Iff.rfl
  done


end HyperTree
