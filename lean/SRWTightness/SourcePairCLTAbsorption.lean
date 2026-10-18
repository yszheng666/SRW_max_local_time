import SRWTightness.SourcePairTiltApproximation
import SRWTightness.SourceGreenScaleComparison

open Filter
open scoped Topology

namespace SRWTightness

/-- The absolute pair CLT error is absorbed uniformly in every nonnegative deficit window. -/
theorem source_pair_CLT_window_absorption :
    ∀ᶠ t : ℝ in atTop, ∀ (h f : ℝ) (l : ℕ),
      0 < h → h ≤ sourceLowerTime (sourceLowerRadius t) → 0 ≤ f →
      sourceTiltApproximationConstant 1 6 (2 * sourceObservationDimensionConstant) (1 / 16) *
          sourceLowerTime (sourceLowerRadius t) ^ 5 / t ≤
        (f + l + 1) / (sourceLowerTime (sourceLowerRadius t) * h) := by
  have herr := source_pair_tilt_error_scaled_tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [herr, eventually_ge_atTop (sourceScaleThreshold 4)] with t he ht
  intro h f l hh hhd hf
  have hd := sourceLowerTime_ge_one t ht
  have hd0 : 0 < sourceLowerTime (sourceLowerRadius t) := by linarith
  rw [Real.rpow_two] at he
  have hδ : sourceTiltApproximationConstant 1 6 (2 * sourceObservationDimensionConstant)
      (1 / 16) * sourceLowerTime (sourceLowerRadius t) ^ 5 / t ≤
      1 / sourceLowerTime (sourceLowerRadius t) ^ 2 :=
    (le_div_iff₀ (pow_pos hd0 2)).mpr (by linarith)
  have hp : 0 < sourceLowerTime (sourceLowerRadius t) * h := mul_pos hd0 hh
  have hsq : sourceLowerTime (sourceLowerRadius t) * h ≤
      sourceLowerTime (sourceLowerRadius t) ^ 2 := by nlinarith
  exact hδ.trans ((one_div_le_one_div_of_le hp hsq).trans
    (div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) l]) hp.le))

end SRWTightness
