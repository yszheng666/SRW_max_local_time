import SRWTightness.SetHitting

open MeasureTheory

namespace SRWTightness

/-- Enlarging the observed set increases the actual killed occupation count. -/
theorem setOccupation_mono_target (D K L : Finset Site) (hKL : K ⊆ L)
    (x : Site) (ω : Sample) : setOccupation D K x ω ≤ setOccupation D L x ω := by
  unfold setOccupation
  exact Finset.sum_le_sum_of_subset_of_nonneg hKL (fun _ _ _ ↦ Nat.zero_le _)

/-- Actual hitting probability is monotone in the target, with the killing domain unchanged. -/
theorem setHitProbability_mono_target (D K L : Finset Site) (hKL : K ⊆ L) (x : Site) :
    setHitProbability D K x ≤ setHitProbability D L x := by
  apply integral_mono (integrable_setHitIndicator D K x) (integrable_setHitIndicator D L x)
  intro ω
  have hh := setOccupation_mono_target D K L hKL x ω
  unfold setHitIndicator
  split_ifs <;> norm_num at * <;> omega

end SRWTightness
