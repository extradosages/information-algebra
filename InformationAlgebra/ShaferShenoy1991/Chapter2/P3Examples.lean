import InformationAlgebra.ShaferShenoy1991.Chapter2.P1HyperGraph
import InformationAlgebra.ShaferShenoy1991.Chapter2.P2HyperTree

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

theorem edge4_supports_edge1

#check Finset.induction_on hyperGraph

theorem edge1_branch_edge4 : Branch hyperGraph edge1 edge4 := by
  constructor
  · intro h
    dsimp only [edge1, edge4] at h
    contradiction
  · constructor
    · exact (bne_iff_ne (edge1 ∩ edge4) ∅).mp rfl
    · whnf
      intros c h_c_in h_c_ne x h_x_in
      repeat cases h_c_in

  done

end Example1
