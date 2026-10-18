import SRWTightness.SubGaussianBinCover

open MeasureTheory Filter Set
open scoped ENNReal
namespace SRWTightness

/-- Summing the unit-bin integrals gives a uniform finite nonnegative moment envelope. -/
theorem sub_gaussian_positive_weight_lintegral_bound (A b : ℝ) (hA : 0 < A) (hb : 0 < b)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hTail : ∀ u : ℝ, 0 ≤ u → ν.real (Ici u) ≤ A * Real.exp (-b * u ^ 2)) :
    (∫⁻ u, ENNReal.ofReal (subGaussianPositiveWeight b u) ∂ν) ≤
      1 + ∑' n : ℕ, ENNReal.ofReal (subGaussianBinBound A b n) := by
  calc
    _ ≤ ∫⁻ u, 1 + ∑' n : ℕ, subGaussianBinIndicator b n u ∂ν :=
      lintegral_mono (sub_gaussian_positive_weight_bin_cover b hb)
    _ = 1 + ∑' n : ℕ, ∫⁻ u, subGaussianBinIndicator b n u ∂ν := by
      rw [lintegral_add_left measurable_const,
        lintegral_tsum (fun n ↦ (sub_gaussian_bin_indicator_measurable b n).aemeasurable)]
      simp
    _ ≤ 1 + ∑' n : ℕ, ENNReal.ofReal (subGaussianBinBound A b n) := by
      exact add_le_add (le_refl (1 : ℝ≥0∞))
        (ENNReal.tsum_le_tsum (sub_gaussian_bin_integral_bound A b hA hb ν hTail))

/-- The original sub-Gaussian positive exponential-moment interface is internally proved. -/
theorem sub_gaussian_positive_moment_input_internal : SubGaussianPositiveMomentInput := by
  intro A b hA hb
  let H : ℝ≥0∞ := 1 + ∑' n : ℕ, ENNReal.ofReal (subGaussianBinBound A b n)
  have hH : H < ⊤ := by
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.one_lt_top, (sub_gaussian_bin_bound_summable A b hb).tsum_ofReal_lt_top⟩
  refine ⟨H.toReal + 1, by positivity, ?_⟩
  intro ν instν hTail
  have hBound : (∫⁻ u, ENNReal.ofReal (subGaussianPositiveWeight b u) ∂ν) ≤ H :=
    sub_gaussian_positive_weight_lintegral_bound A b hA hb ν hTail
  have hnonneg : ∀ u : ℝ, 0 ≤ subGaussianPositiveWeight b u := fun _ ↦ Real.exp_nonneg _
  have hm : AEStronglyMeasurable (subGaussianPositiveWeight b) ν :=
    (show Continuous (subGaussianPositiveWeight b) by
      unfold subGaussianPositiveWeight
      fun_prop).measurable.aestronglyMeasurable
  have hi : Integrable (subGaussianPositiveWeight b) ν := by
    refine ⟨hm, ?_⟩
    change (∫⁻ u, ‖subGaussianPositiveWeight b u‖ₑ ∂ν) < ⊤
    apply lt_of_le_of_lt ?_ hH
    calc
      _ ≤ ∫⁻ u, ENNReal.ofReal (subGaussianPositiveWeight b u) ∂ν :=
        lintegral_mono (fun u ↦ (Real.enorm_eq_ofReal (hnonneg u)).le)
      _ ≤ H := hBound
  refine ⟨hi, ?_⟩
  change (∫ u, subGaussianPositiveWeight b u ∂ν) ≤ H.toReal + 1
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnonneg) hm]
  exact (ENNReal.toReal_mono hH.ne hBound).trans (le_add_of_nonneg_right (by norm_num))

end SRWTightness
