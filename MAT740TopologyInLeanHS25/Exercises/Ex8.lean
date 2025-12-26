import Mathlib.Tactic
import MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces
import MAT740TopologyInLeanHS25.Definitions.Filters

open MyFilter

variable {X Y : Type*} {A B : Set X}

section Ex1

lemma max_tail' {s : ℕ → X} {nA nB : ℕ}
(hn : tail s nA ⊆ A) (hm : tail s nB ⊆ B)
: tail s (max nA nB) ⊆ A ∩ B := by
  sorry -- exercise

def eventuality' (s : ℕ → X) : MyFilter.Filter X where
  Sets := {A | ∃ n, tail s n ⊆ A}
  /- exercise -/
  univ_Sets := by sorry
  upward_Sets := by sorry
  inter_Sets := by sorry -- hint: use `max_tail'`

end Ex1

section Ex2

theorem Cont_convergence' [Topology X] [Topology X] (f : X → Y)
  : Cont f ↔ ∀ (G : MyFilter.Filter X) (x : X), G lim x → (mapFilter f G) lim (f x) := by
    constructor
    case mp => sorry -- no need to fill this in
    case mpr =>
      intro h U open_U
      have g : ∀ x ∈ f ⁻¹' U, ∃ V, Nbhd V x ∧ V ⊆ f ⁻¹' U := by
        sorry -- exercise
        /- Hints:
        Let `F := NbhdFilter x`.
        Show that `F lim x` and use the hypothesis `h`.
        Show that `f ⁻¹' U ∈ F`. This is an existential statement you can deconstruct.-/
      choose V g using g
      have union_fU : f ⁻¹' U = ⋃₀ {B | ∃ (x : X) (w : x ∈ f ⁻¹' U), B = V x w} := by
        sorry -- exercise
      rw [union_fU]
      apply Open_sUnion
      intro W hW
      obtain ⟨x,wx,hx⟩ := hW
      specialize g x wx
      rw [hx]
      exact g.1.1

end Ex2
