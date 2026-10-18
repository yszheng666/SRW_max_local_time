import SRWTightness.SourcePairShellGeometry
import SRWTightness.StretchedExponentialSumInput

namespace SRWTightness

/-- The standard separated-mesh estimate applies to the actual SRW shell deficits. -/
theorem source_pair_shell_series_bound (hSum : SeparatedStretchedExponentialSumInput)
    (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t A : ℝ),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      sourceEquilibriumTimeError + sourceLowerTimeError + 1 ≤ Real.log A →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      let h := fun i ↦ sourceLowerTime (sourceLowerRadius t) -
        sourceObservationTime t A I (I - i + 1)
      (∑ i ∈ Finset.range (I + 1), ((1 + (h i) ^ γ) / h i) *
        Real.exp (-c * (h i) ^ γ)) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hSum 1 1 c γ (by norm_num) (by norm_num) hc hγ
  refine ⟨C, hC, ?_⟩
  intro t A hA ht hlog I hI
  apply hbound I
  · intro i hi
    exact ((source_pair_shell_deficit_bounds t A hA ht hlog I hI).1 i hi).1
  · intro i hi
    exact source_pair_shell_deficit_gap t A hA ht I hI i hi

/-- Summing the large-deficit Chernoff contribution costs at most d² times its endpoint factor. -/
theorem source_pair_shell_chernoff_sum (t A γ : ℝ) (hγ : 0 ≤ γ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : sourceEquilibriumTimeError + sourceLowerTimeError + 1 ≤ Real.log A)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) :
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := fun i ↦ d - sourceObservationTime t A I (I - i + 1)
    (∑ i ∈ Finset.range (I + 1),
      if d / 2 < h i then d * Real.exp (-2 * (h i) ^ γ) else 0) ≤
      d ^ 2 * Real.exp (-2 * (d / 2) ^ γ) := by
  classical
  dsimp only
  let d := sourceLowerTime (sourceLowerRadius t)
  have hb := source_pair_shell_deficit_bounds t A hA ht hlog I hI
  have hd : 0 ≤ d := by dsimp [d]; have hh := (hb.1 0 (Nat.zero_le I)); linarith
  calc
    _ ≤ ∑ _i ∈ Finset.range (I + 1), d * Real.exp (-2 * (d / 2) ^ γ) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with hh
      · apply mul_le_mul_of_nonneg_left _ hd
        apply Real.exp_le_exp.mpr
        have hr := Real.rpow_le_rpow (by positivity : 0 ≤ d / 2) hh.le hγ
        linarith
      · positivity
    _ = ((I + 1 : ℕ) : ℝ) * (d * Real.exp (-2 * (d / 2) ^ γ)) := by simp
    _ ≤ d * (d * Real.exp (-2 * (d / 2) ^ γ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hb.2) (mul_nonneg hd (Real.exp_nonneg _))
    _ = _ := by ring

end SRWTightness
