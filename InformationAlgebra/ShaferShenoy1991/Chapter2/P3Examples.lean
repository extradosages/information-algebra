import InformationAlgebra.ShaferShenoy1991.Chapter2.P1HyperGraph
import InformationAlgebra.ShaferShenoy1991.Chapter2.P2HyperTree
import Mathlib.Tactic.FinCases
import Mathlib

open HyperGraph
open HyperTree

namespace Example

namespace Tactic


syntax "decidable_eq_enum" : tactic
macro_rules
  | `(tactic| decidable_eq_enum) =>
    `(tactic|
      intros a b;
      cases a <;>
      cases b <;>
      (try apply Decidable.isTrue rfl) <;>
      (try apply Decidable.isFalse; simp_all only [not_false_eq_true])
    )


syntax "supports" : tactic
macro_rules
  | `(tactic| supports) =>
    `(tactic|
      intros edge h_edge_in_H _ _ h_vertex_in_inter;
      dsimp only [Membership.mem] at h_edge_in_H;
      dsimp only [HyperGraph.mem, HyperGraph.toFinset] at h_edge_in_H;
      refine And.elim ?f (Finset.mem_inter.mp h_vertex_in_inter);
      intros h_vertex_in₁ h_vertex_in₂;
      fin_cases h_vertex_in₁ <;> fin_cases h_edge_in_H;
      all_goals repeat (first | contradiction | decide)
    )


syntax "inter" ident : tactic
macro_rules
  | `(tactic| inter $elt:ident) =>
    `(tactic| exact Exists.intro $elt <| Finset.mem_inter.mpr ⟨by decide, by decide⟩)


syntax "branch" ident : tactic
macro_rules
  | `(tactic| branch $elt:ident) =>
    `(tactic| exact ⟨by decide, by inter $elt, by supports⟩)


end Tactic

open Tactic

namespace Example1

inductive Element
  | S | T | U | V | W | X | Y | Z

open Element

instance : DecidableEq Element := by decidable_eq_enum

def edge₁ : HyperEdge Element := {S, T, V}
def edge₂ : HyperEdge Element := {U, X}
def edge₃ : HyperEdge Element := {U, V, W}
def edge₄ : HyperEdge Element := {T, V, W, X}
def edge₅ : HyperEdge Element := {W, Y, Z}

def ℋ : HyperGraph Element := {edge₁, edge₂, edge₃, edge₄, edge₅}

theorem branch_edge₄_edge₁ : ℋ.Branch edge₄ edge₁ := by branch V

theorem branch_edge₄_edge₅ : ℋ.Branch edge₄ edge₅ := by branch W

theorem branch_edge3_edge4 : ℋ.Branch edge₃ edge₅ := by branch W

/- TODO: Shafer and Shenoy make a point of highlighting that these are the only branches in this
hypergraph, so maybe we should include some proofs that other pairs of edges are not branches. -/

end Example1


namespace Example2

inductive Element where
  | W | X | Y | Z

open Element

instance : DecidableEq Element := by decidable_eq_enum

def edge₁ : HyperEdge Element := {W, X}
def edge₂ : HyperEdge Element := {X, Y}
def edge₃ : HyperEdge Element := {X, Z}
def edge₄ : HyperEdge Element := {Y, Z}
def edge₅ : HyperEdge Element := {W, Y}
def edge₆ : HyperEdge Element := {X, Y, Z}

def ℋ₁ : HyperGraph Element := {edge₁, edge₂, edge₃}
def ℋ₂ : HyperGraph Element := {edge₁, edge₂, edge₄}
def ℋ₃ : HyperGraph Element := {edge₁, edge₅, edge₆}

theorem H1_branch_edge₁_edge₂ : ℋ₁.Branch edge₁ edge₂ := by branch X
theorem H1_branch_edge₁_edge₃ : ℋ₁.Branch edge₁ edge₃ := by branch X
theorem H1_branch_edge₂_edge₃ : ℋ₁.Branch edge₂ edge₃ := by branch X
theorem H1_branch_edge₂_edge₁ : ℋ₁.Branch edge₂ edge₁ := by branch X
theorem H1_branch_edge₃_edge₁ : ℋ₁.Branch edge₃ edge₁ := by branch X
theorem H1_branch_edge₃_edge₂ : ℋ₁.Branch edge₃ edge₂ := by branch X

end Example2
