import InformationAlgebra.ShaferShenoy1991.Chapter2.P1HyperGraph
import InformationAlgebra.ShaferShenoy1991.Chapter2.P2HyperTree
import Mathlib.Tactic.FinCases
import Mathlib

open HyperGraph

namespace Example

namespace Example1

inductive Element
  | S | T | U | V | W | X | Y | Z

instance : DecidableEq Element := by
  intros a b
  cases a <;> cases b
  all_goals (try apply Decidable.isTrue rfl)
  all_goals (try apply Decidable.isFalse; simp_all only [not_false_eq_true])
  done

open Element

def edge1 : HyperEdge Element := {S, T, V}
def edge2 : HyperEdge Element := {U, X}
def edge3 : HyperEdge Element := {U, V, W}
def edge4 : HyperEdge Element := {T, V, W, X}
def edge5 : HyperEdge Element := {W, Y, Z}

def hyperGraph : HyperGraph Element := {edge1, edge2, edge3, edge4, edge5}

theorem supports_edge4_edge1 : HyperGraph.Supports hyperGraph edge4 edge1 := by
  intros edge h_edge_in_hyperGraph h_edge_ne_edge4 vertex h_vertex_in_inter
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

theorem branch_edge4_edge1 : Branch hyperGraph edge4 edge1 := by
  constructor
  · exact edge4_ne_edge1
  · constructor
    · exact (bne_iff_ne (edge4 ∩ edge1) ∅).mp rfl
    · exact supports_edge4_edge1
  done

theorem supports_edge4_edge5 : HyperGraph.Supports hyperGraph edge4 edge5 := by
  intros edge h_edge_in_hyperGraph h_edge_ne_edge4 vertex h_vertex_in_inter
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

theorem branch_edge5_edge4 : Branch hyperGraph edge4 edge5 := by
  constructor
  · exact edge4_ne_edge5
  · constructor
    · exact (bne_iff_ne (edge4 ∩ edge5) ∅).mp rfl
    · exact supports_edge4_edge5
  done

theorem supports_edge3_edge5 : HyperGraph.Supports hyperGraph edge3 edge5 := by
  intros edge h_edge_in_hyperGraph h_edge_ne_edge4 vertex h_vertex_in_inter
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

theorem branch_edge3_edge4 : Branch hyperGraph edge3 edge5 := by
  constructor
  · exact edge3_ne_edge5
  · constructor
    · exact (bne_iff_ne (edge3 ∩ edge5) ∅).mp rfl
    · exact supports_edge3_edge5
  done
