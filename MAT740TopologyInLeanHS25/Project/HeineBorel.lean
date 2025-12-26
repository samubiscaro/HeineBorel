import Mathlib.Tactic

import MAT740TopologyInLeanHS25.Definitions.MetricSpaces
import MAT740TopologyInLeanHS25.Definitions.Filters
import MAT740TopologyInLeanHS25.Definitions.Compactness
import MAT740TopologyInLeanHS25.Project.CompleteSpaces
import MAT740TopologyInLeanHS25.Project.BoundedSpaces

universe u

theorem Compact_iff_Complete_and_totallyBounded {X : Type u} [MetricSpace X] :
    Compact (Set.univ : Set X) ↔ Complete X ∧ totallyBounded X := by
  -- Use the new definitions
  rw [← filterCompact_iff_Compact]
  rw [complete_iff_filterComplete]
  rw [totallyBounded_iff_filterTotallyBounded]
  constructor
  case mp =>
    intro h
    constructor
    · -- Compact → Complete
      -- Take a Cauchy filter F ...
      intro F hC
      -- ... extend it to an ultrafilter U ...
      obtain ⟨U, hU, hFU⟩ := ultraFilter_extension F hC.1
      rw [MyFilter.ultra_iff_prime] at hU
      -- ... U converges because X is compact ...
      specialize h U hU
      -- ... and so does F because F ⊆ U and F is Cauchy
      exact CauchyFilter_converge_to_adeherent F U hC
        (by
          intro A B l hl hA hB
          have w : A ∩ B ∈ U := by exact U.inter_Sets (hFU hA) (hl hB)
          intro h
          rw [h] at w
          obtain ⟨hU, _ ⟩ := hU
          contradiction
        ) h
    · -- Compact → totallyBounded
      -- Take an ultrafilter U ...
      intro F hF
      rw [MyFilter.ultra_iff_prime] at hF
      -- ... it converges and so it is a Cauchy filter
      exact convergentFilt_is_Cauchy F hF.1 (h F hF)
  case mpr =>
    -- Complete ∧ totallyBounded → Compact
    -- Take an ultrafilter F ...
    intro ⟨hC, hB⟩ F hF
    rw [← MyFilter.ultra_iff_prime] at hF
    -- ... F is a Cauchy filter since X is totally bounded ...
    specialize hB F hF
    -- ... but then F converges since X is complete
    obtain ⟨l, hl⟩ := hC F hB
    use l
