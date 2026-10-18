import SRWTightness.SourceScaleProfile
import SRWTightness.SourceGaussianParameters

namespace SRWTightness

noncomputable def sourceObservationDimensionConstant : ℝ :=
  (1 + sourceLowerTimeError) / Real.log diskEnergyGapRatio + 2

theorem sourceObservationDimensionConstant_pos : 0 < sourceObservationDimensionConstant := by
  have hE := sourceLowerTimeError_pos
  have hl := Real.log_pos (show 1 < diskEnergyGapRatio by linarith [diskEnergyGapRatio_gt_four])
  unfold sourceObservationDimensionConstant
  positivity

/-- The full ordered vector, including the center point, satisfies the actual dimension bound. -/
theorem source_observation_dimension (t A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : sourceGaussianThreshold A ≤ t) (I : ℕ)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) :
    (Fintype.card (Fin ((I + 1) + 1)) : ℝ) ≤
      sourceObservationDimensionConstant * sourceLowerTime (sourceLowerRadius t) := by
  have ha : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have htbase : sourceScaleThreshold A ≤ t := (le_max_left _ _).trans ht
  have hq : 1 < diskEnergyGapRatio := by linarith [diskEnergyGapRatio_gt_four]
  obtain ⟨J, hJ, _, _, hdim⟩ := source_scale_profile 0 t A diskEnergyGapRatio ha hq htbase
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  obtain ⟨_, _, hm, hdlog⟩ := sourceScaleThreshold_conditions t A ha htbase
  have hd : 1 ≤ sourceLowerTime (sourceLowerRadius t) := by
    have hh := (abs_le.mp (sourceLowerTime_log_bound (sourceLowerRadius t) (by linarith))).1
    linarith
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  unfold sourceObservationDimensionConstant
  nlinarith

end SRWTightness
