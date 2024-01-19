import Mathlib


namespace HyperGraph


variable
  (X : Type*)


abbrev Vertex := X


abbrev HyperEdge := Set X


abbrev HyperGraph := Finset (HyperEdge X)


def isBranch
    {X}
    (hyperGraph : HyperGraph X)
    (b : HyperEdge X)
    (t : HyperEdge X)
    :
    Prop
    :=
  b ∩ t ≠ ∅ ∧ ∀ h ∈ hyperGraph, h ≠ t → ∀ x ∈ t, x ∈ h → x ∈ b


def IsTwig
    {X}
    (hyperGraph : HyperGraph X)
    (t : HyperEdge X)
    (b : HyperEdge X)
    :
    Prop
    :=
  isBranch hyperGraph b t


def Twig (hyperGraph : HyperGraph X) := {t : HyperEdge X | ∃ b : hyperGraph, IsTwig hyperGraph t b }


example (l : List α) : Finset α := by
  apply?
  done


/-- `Chain R a l` means that `R` holds between adjacent elements of `a::l`.
```
Chain R a [b, c, d] ↔ R a b ∧ R b c ∧ R c d
``` -/
inductive HyperTree : (t : HyperEdge X) → (H : Finset (HyperEdge X)) → (p : t ∉ H) → Prop
  | nil {a : HyperEdge X} : HyperTree a ∅ _
  | cons : ∀ {a b : HyperEdge X} {l : Finset (HyperEdge X)}, IsTwig l a b → HyperTree b l q → HyperTree a (Finset.cons b l q) p
