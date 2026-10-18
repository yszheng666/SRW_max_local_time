import SRWTightness.SourceReferenceCapacity
import SRWTightness.SourcePairDeficitDistance

namespace SRWTightness

/-- The actual maximal cutoff supplies all support and mass conditions for a retained pair average. -/
theorem source_pair_observation_geometry (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I) :
    let m := sourceLowerRadius t
    let a := A * diskEnergyGapRatio ^ i
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
    1 ≤ a ∧ 2 * a ≤ m ∧ M ⊆ D ∧ translateFinset b (diskFinset a) ⊆ M ∧
      sourceReferenceIntensity m 14 * capacity D M ≤ 1 := by
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hB : 1 ≤ diskEnergyGapRatio := by linarith [diskEnergyGapRatio_gt_four]
  have hpow : 1 ≤ diskEnergyGapRatio ^ i := one_le_pow₀ hB
  have ha : 1 ≤ A * diskEnergyGapRatio ^ i := by nlinarith
  have hmono : A * diskEnergyGapRatio ^ i ≤ A * diskEnergyGapRatio ^ I :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hi) (by linarith)
  have hs := sourceScaleThreshold_conditions t A ha4 ((le_max_left _ _).trans ht)
  have ht2 : 2 ≤ t := hs.1
  have ht6 : (2 : ℝ) ≤ t ^ 6 := ht2.trans (by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ t) (by norm_num : 1 ≤ 6))
  have hcut := (le_div_iff₀ (by positivity : 0 < t ^ 6)).mp ((hI I).mpr le_rfl)
  have hmax : 2 * (A * diskEnergyGapRatio ^ I) ≤ sourceLowerRadius t := by nlinarith
  have houter : A * diskEnergyGapRatio ^ I ≤ Real.exp 1 * sourceLowerRadius t + 14 := by
    nlinarith [sourceLowerRadius_pos t, Real.exp_one_gt_two]
  obtain ⟨J, hJ, hcap⟩ := source_reference_capacity b t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  dsimp only
  refine ⟨ha, by linarith, ?_, ?_, hcap⟩
  · apply Finset.image_subset_image
    exact diskFinset_mono _ _ (by linarith) houter
  · apply Finset.image_subset_image
    exact diskFinset_mono _ _ (by linarith) hmono

end SRWTightness
