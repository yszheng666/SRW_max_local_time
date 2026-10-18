import SRWTightness.SourceCommonPairCoarseReferenceSum
import SRWTightness.SourceCommonPairLevelRange

open Filter
namespace SRWTightness

/-- The full source range of later common coarse levels. -/
noncomputable def sourceCommonLevels (t : ℝ) : Finset ℕ :=
  (Finset.range (sourceRootDepth (Real.exp t) (sourceLowerRadius t))).filter
    (fun j ↦ sourceCoarseLowerLevel t ≤ j)

/-- The number of permitted common levels is at most t+1. -/
theorem source_common_levels_card :
    ∀ᶠ t : ℝ in atTop, ((sourceCommonLevels t).card : ℝ) ≤ t + 1 := by
  filter_upwards [source_common_pair_level_range, eventually_ge_atTop (0 : ℝ)] with t hr ht
  have hsub : sourceCommonLevels t ⊆ Finset.range (⌊t⌋₊ + 1) := by
    intro j hj
    obtain ⟨hjrange, _⟩ := Finset.mem_filter.mp hj
    have hd : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
      have hh := Finset.mem_range.mp hjrange
      omega
    have hh : j ≤ ⌊t⌋₊ := Nat.le_floor (hr j hd).1
    exact Finset.mem_range.mpr (by omega)
  have hc : ((sourceCommonLevels t).card : ℝ) ≤ (⌊t⌋₊ : ℝ) + 1 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_range] at hh
    exact_mod_cast hh
  linarith [Nat.floor_le ht]

end SRWTightness
