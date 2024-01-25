import InformationAlgebra.ShaferShenoy1991.Chapter2.P1HyperGraph


/-!
# HyperTree

This file introduces hypertrees.
-/

open HyperGraph


namespace HyperTree


variable
  {X : Type}
  [inst : DecidableEq X]


/-- The type of all proofs that a list of hyperedges can be decomposed into the sequential
addition of twigs.

Note that this type does not require that a twig involved in the construction sequence is disjoint
at each step. Although this is essential in the definition of a `HyperTree`, it has been excluded
from this type for accessibility reasons. That constraint is instead folded into the `HyperTree`
type itself, as a separate `List.Nodup` proof. -/
inductive ConsTwig : (HyperEdge X) → (List (HyperEdge X)) → Prop where
  /-- Any trivial hypergraph is a vacuously a hypertree.

  Note that a trivial hypergraph has one edge. -/
  | nil  : ∀ {a : HyperEdge X}, ConsTwig a []
  /-- By providing a proof that an edge `a` is a twig for the hypergraph comprised of the elements
  of a nonempty list `b::l` and a proof that `b::l` is itself constructed of twigs, we obtain a
  proof that the `a::b::l` is itself constructed by twigs. -/
  | cons : ∀ {a b : HyperEdge X} {l : List (HyperEdge X)}, (HyperGraph.Twig' (List.toHyperGraph b l) a) → (ConsTwig b l) → ConsTwig a (b::l)

attribute [simp] ConsTwig.nil
attribute [simp] ConsTwig.cons


/-- A `HyperTree` is a `HyperGraph`, together with an ordering of its edges such that each edge is
a twig for the hypergraph given by its downward section in the ordering.
-/
structure HyperTree (X : Type) [inst : DecidableEq X] where
  /-- The most recent edge added to the hypertree.

  Note that this is not the root. -/
  head : HyperEdge X
  /-- Other edges in the hypertree. -/
  tail : List (HyperEdge X)
  /-- No edges in a hypertree are repeated. -/
  nodup : (head::tail).Nodup
  /-- The hypertree is constructed by twigs. -/
  constwig : @ConsTwig X inst head tail


def HyperTree.toList (𝒯 : HyperTree X) : List (HyperEdge X) := 𝒯.head::𝒯.tail


theorem toList_nonempty {𝒯 : HyperTree X} : 𝒯.toList ≠ [] := List.getLast?_isSome.mp rfl


def HyperTree.toHyperGraph (𝒯 : HyperTree X) : HyperGraph X :=
  ⟨𝒯.toList.toFinset, List.toFinset_nonempty_iff (HyperTree.toList 𝒯) |>.mpr toList_nonempty⟩


instance : Coe (HyperTree X) (HyperGraph X) := ⟨HyperTree.toHyperGraph⟩


instance : Singleton (HyperEdge X) (HyperTree X) where
  singleton a := ⟨a, [], List.nodup_singleton a, ConsTwig.nil⟩


theorem coe_singleton {a : HyperEdge X} :  ({a} : HyperTree X) = ({a} : HyperGraph X) := rfl


instance : Membership (HyperEdge X) (HyperTree X) where
  mem a 𝒯 := a ∈ 𝒯.toList


@[simp]
theorem mem_cases {a : HyperEdge X} {𝒯 : HyperTree X} : (a ∈ 𝒯) ↔ a = 𝒯.head ∨ a ∈ 𝒯.tail :=
  List.mem_cons


theorem mem_singleton {a b : HyperEdge X} : a ∈ ({b} : HyperTree X) ↔ a = b := List.mem_singleton


theorem coe_mem {a : HyperEdge X} {𝒯 : HyperTree X} : a ∈ 𝒯 ↔ a ∈ (𝒯 : HyperGraph X) := by
  constructor <;> intro h
  · exact List.mem_toFinset.mpr h
  · exact List.mem_toFinset.mp h
  done


theorem nodup_tail (𝒯 : HyperTree X) : 𝒯.tail.Nodup := List.nodup_cons.mp 𝒯.nodup |>.right


theorem head_nin_tail (𝒯 : HyperTree X) : 𝒯.head ∉ 𝒯.tail := List.nodup_cons.mp 𝒯.nodup |>.left


theorem disjoint_edge_ne_head (𝒯 : HyperTree X) (a : HyperEdge X) (h : a ∉ 𝒯) : a ≠ 𝒯.head := by
  simp only [mem_cases] at h
  intro h₂
  exact absurd (h₂) (not_or.mp h |>.left)
  done


theorem disjoint_edge_nin_tail (𝒯 : HyperTree X) (a : HyperEdge X) (h : a ∉ 𝒯) : a ∉ 𝒯.tail := by
  simp only [mem_cases] at h
  exact not_or.mp h |>.right
  done


theorem cons_list_nodup (𝒯 : HyperTree X) (a : HyperEdge X) (h : a ∉ 𝒯) : List.Nodup (a :: 𝒯.head :: 𝒯.tail) := by
    simp only [List.nodup_cons, Bool.not_eq_true, List.mem_cons]
    refine ⟨?_, head_nin_tail 𝒯, nodup_tail 𝒯⟩
    intro h₂
    apply Or.elim h₂
    · intro h₃
      exact absurd h₃ (disjoint_edge_ne_head 𝒯 a h)
    · intro h₃
      exact absurd h₃ (disjoint_edge_nin_tail 𝒯 a h)


theorem cons_twig (𝒯 : HyperTree X) (a : @HyperGraph.DisjointTwig X inst 𝒯) : ConsTwig a (𝒯.head :: 𝒯.tail) :=
  ConsTwig.cons a.property.right 𝒯.constwig


-- TODO: Figure out why `HyperGraph.DisjointTwig` needs so much help.
/-- Attach a new twig to a hypertree, producing another hypertree. -/
def HyperTree.cons (𝒯 : HyperTree X) (a : @HyperGraph.DisjointTwig X inst 𝒯) : HyperTree X := ⟨
    a,
    (𝒯.head::𝒯.tail),
    cons_list_nodup 𝒯 a (Iff.not coe_mem |>.mpr a.property.left),
    cons_twig 𝒯 a
  ⟩


@[inherit_doc]
infixl:70 " ::ₛ "  => HyperTree.cons


theorem mem_cons {𝒯 : HyperTree X} {a : @HyperGraph.DisjointTwig X inst 𝒯} {b : HyperEdge X} : b ∈ (𝒯::ₛa) ↔ b ∈ 𝒯 ∨ b = a := by
  constructor <;> intro h
  · cases h with
      | head _ => exact Or.inr rfl
      | tail _ h₂ => exact Or.inl h₂
  · dsimp only [Membership.mem] at *
    dsimp only [HyperTree.cons, HyperTree.toList] at *
    apply Or.elim h <;> intro h₂
    · exact List.Mem.tail _ h₂
    · rw [h₂]
      exact List.Mem.head _
  done


end HyperTree
