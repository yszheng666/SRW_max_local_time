import SRWTightness.ExponentialSumMoments

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The uniform Gamma-type comparison for the actual sum of independent holding times. -/
theorem exponential_selected_sum_ge_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → κ) (hj : Function.Injective j) (hcard : 0 < Fintype.card ι) :
    (1 / 36 : ℝ) ≤ (Measure.pi (fun _ : κ ↦ expMeasure 1)).real
      {T : κ → ℝ | (Fintype.card ι : ℝ) ≤ ∑ i : ι, T (j i)} := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  let μ := Measure.pi (fun _ : κ ↦ expMeasure 1)
  let X := fun T : κ → ℝ ↦ ∑ i : ι, (T (j i) - 1)
  obtain ⟨hI, hc, h2, h4⟩ := exponential_selected_sum_moments j hj
  have hp : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
  have hp1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have hX : Integrable X μ := by simpa only [pow_one] using hI 1 (by decide)
  have hXm : Measurable X := by dsimp [X]; fun_prop
  have hp2 : 0 < ∫ T, X T ^ 2 ∂μ := by rw [h2]; exact hp
  have hp4 : 0 < ∫ T, X T ^ 4 ∂μ := by rw [h4]; positivity
  have hb := positive_probability_lower_of_centered μ X hXm hX
    (hI 2 (by decide)) (hI 4 (by decide)) hc hp2 hp4
  rw [h2, h4] at hb
  have hl : (1 / 36 : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 /
      (4 * (3 * (Fintype.card ι : ℝ) ^ 2 + 6 * Fintype.card ι)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hp1)]
  apply hl.trans (hb.trans ?_)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro T hT
  change 0 < ∑ i : ι, (T (j i) - 1) at hT
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hT
  exact le_of_lt (sub_pos.mp hT)

end SRWTightness
