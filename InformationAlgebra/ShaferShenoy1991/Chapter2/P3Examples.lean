import InformationAlgebra.ShaferShenoy1991.Chapter2.P1HyperGraph
import InformationAlgebra.ShaferShenoy1991.Chapter2.P2HyperTree
import Mathlib.Tactic.FinCases
import Mathlib

open HyperGraph
open HyperTree

namespace Example

namespace Example1

inductive Element
  | S | T | U | V | W | X | Y | Z

instance : DecidableEq Element := by
  intros a b
  cases a <;>
    cases b <;>
      (try apply Decidable.isTrue rfl) <;>
        (try apply Decidable.isFalse; simp_all only [not_false_eq_true])
  done

open Element

def edge1 : HyperEdge Element := {S, T, V}
def edge2 : HyperEdge Element := {U, X}
def edge3 : HyperEdge Element := {U, V, W}
def edge4 : HyperEdge Element := {T, V, W, X}
def edge5 : HyperEdge Element := {W, Y, Z}

def ℋ : HyperGraph Element := {edge1, edge2, edge3, edge4, edge5}

-- TODO: Extract into tactic
theorem supports_edge4_edge1 : ℋ.Supports edge4 edge1 := by
  intros edge h_edge_in_hyperGraph _ _ h_vertex_in_inter
  dsimp only [Membership.mem] at h_edge_in_hyperGraph
  dsimp only [HyperGraph.mem, HyperGraph.toFinset] at h_edge_in_hyperGraph
  refine And.elim ?f (Finset.mem_inter.mp h_vertex_in_inter)
  intros h_vertex_in₁ h_vertex_in₂
  fin_cases h_vertex_in₁ <;> fin_cases h_edge_in_hyperGraph
  all_goals repeat (first | contradiction | apply List.Mem.head | apply List.Mem.tail)
  done

theorem edge4_ne_edge1 : edge4 ≠ edge1 := by
  exact (bne_iff_ne edge4 edge1).mp rfl
  done

theorem branch_edge4_edge1 : ℋ.Branch edge4 edge1 := by
  constructor
  · exact edge4_ne_edge1
  · constructor
    · exact (bne_iff_ne (edge4 ∩ edge1) ∅).mp rfl
    · exact supports_edge4_edge1
  done

theorem supports_edge4_edge5 : ℋ.Supports edge4 edge5 := by
  intros edge h_edge_in_hyperGraph _ _ h_vertex_in_inter
  dsimp only [Membership.mem] at h_edge_in_hyperGraph
  dsimp only [HyperGraph.mem, HyperGraph.toFinset] at h_edge_in_hyperGraph
  refine And.elim ?f (Finset.mem_inter.mp h_vertex_in_inter)
  intros h_vertex_in₁ h_vertex_in₂
  fin_cases h_vertex_in₁ <;> fin_cases h_edge_in_hyperGraph
  all_goals repeat (first | contradiction | apply List.Mem.head | apply List.Mem.tail)
  done

theorem edge4_ne_edge5 : edge4 ≠ edge5 := by
  exact (bne_iff_ne edge4 edge5).mp rfl
  done

theorem branch_edge5_edge4 : ℋ.Branch edge4 edge5 := by
  constructor
  · exact edge4_ne_edge5
  · constructor
    · exact (bne_iff_ne (edge4 ∩ edge5) ∅).mp rfl
    · exact supports_edge4_edge5
  done

theorem supports_edge3_edge5 : ℋ.Supports edge3 edge5 := by
  intros edge h_edge_in_hyperGraph _ _ h_vertex_in_inter
  dsimp only [Membership.mem] at h_edge_in_hyperGraph
  dsimp only [HyperGraph.mem, HyperGraph.toFinset] at h_edge_in_hyperGraph
  refine And.elim ?f (Finset.mem_inter.mp h_vertex_in_inter)
  intros h_vertex_in₁ h_vertex_in₂
  fin_cases h_vertex_in₁ <;> fin_cases h_edge_in_hyperGraph
  all_goals repeat (first | contradiction | apply List.Mem.head | apply List.Mem.tail)
  done

theorem edge3_ne_edge5 : edge3 ≠ edge5 := by
  exact (bne_iff_ne edge3 edge5).mp rfl
  done

theorem branch_edge3_edge4 : ℋ.Branch edge3 edge5 := by
  constructor
  · exact edge3_ne_edge5
  · constructor
    · exact (bne_iff_ne (edge3 ∩ edge5) ∅).mp rfl
    · exact supports_edge3_edge5
  done

/- TODO: Shafer and Shenoy make a point of highlighting that these are the only branches in this
hypergraph, so maybe we should include some proofs that other pairs of edges are not branches. -/

end Example1


namespace Example2

inductive Element where
  | W | X | Y | Z

open Element

instance : DecidableEq Element := by
  intros a b
  cases a <;>
    cases b <;>
      (try apply Decidable.isTrue rfl) <;>
        (try apply Decidable.isFalse; simp_all only [not_false_eq_true])
  done

def edge₁ : HyperEdge Element := {W, X}
def edge₂ : HyperEdge Element := {X, Y}
def edge₃ : HyperEdge Element := {X, Z}
def edge₄ : HyperEdge Element := {Y, Z}
def edge₅ : HyperEdge Element := {W, Y}
def edge₆ : HyperEdge Element := {X, Y, Z}

def ℋ₁ : HyperGraph Element := {edge₁, edge₂, edge₃}
def ℋ₂ : HyperGraph Element := {edge₁, edge₂, edge₄}
def ℋ₃ : HyperGraph Element := {edge₁, edge₅, edge₆}

theorem H1_edge₁_supports_edge₂ : ℋ₁.Supports edge₁ edge₂ := by
  sorry
  done

end Example2
