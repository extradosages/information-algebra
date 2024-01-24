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


syntax (name := inter) "inter" ident : tactic
macro_rules
  | `(tactic| inter $elt:ident) =>
    `(tactic| exact Exists.intro $elt <| Finset.mem_inter.mpr ⟨by decide, by decide⟩)


end Tactic

open Tactic

namespace Example1

inductive Element
  | S | T | U | V | W | X | Y | Z

instance : DecidableEq Element := by decidable_eq_enum

open Element

def edge₁ : HyperEdge Element := {S, T, V}
def edge₂ : HyperEdge Element := {U, X}
def edge₃ : HyperEdge Element := {U, V, W}
def edge₄ : HyperEdge Element := {T, V, W, X}
def edge₅ : HyperEdge Element := {W, Y, Z}

def ℋ : HyperGraph Element := {edge₁, edge₂, edge₃, edge₄, edge₅}


theorem edge₄_ne_edge₁ : edge₄ ≠ edge₁ := by decide

theorem edge₄_inter_edge₁ : (edge₄ ∩ edge₁).Nonempty := by inter V

theorem supports_edge₄_edge₁ : ℋ.Supports edge₄ edge₁ := by supports

theorem branch_edge₄_edge₁ : ℋ.Branch edge₄ edge₁ :=
  ⟨edge₄_ne_edge₁, edge₄_inter_edge₁, supports_edge₄_edge₁⟩


theorem edge₄_ne_edge₅ : edge₄ ≠ edge₅ := by decide

theorem edge₄_inter_edge₅ : (edge₄ ∩ edge₅).Nonempty := by inter W

theorem supports_edge₄_edge₅ : ℋ.Supports edge₄ edge₅ := by supports

theorem branch_edge₄_edge₅ : ℋ.Branch edge₄ edge₅ :=
  ⟨edge₄_ne_edge₅, edge₄_inter_edge₅, supports_edge₄_edge₅⟩


theorem edge₃_ne_edge₅ : edge₃ ≠ edge₅ := by decide

theorem edge₃_inter_edge₅ : (edge₃ ∩ edge₅).Nonempty := by inter W

theorem supports_edge₃_edge₅ : ℋ.Supports edge₃ edge₅ := by supports

theorem branch_edge3_edge4 : ℋ.Branch edge₃ edge₅ :=
  ⟨edge₃_ne_edge₅, edge₃_inter_edge₅, supports_edge₃_edge₅⟩

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

theorem H1_edge₁_supports_edge₂ : ℋ₁.Supports edge₁ edge₂ := by supports

theorem edge₁_ne_edge₂ : edge₁ ≠ edge₂ := by decide

theorem edge₁_inter_edge₂ : (edge₁ ∩ edge₂).Nonempty := by inter X




end Example2
