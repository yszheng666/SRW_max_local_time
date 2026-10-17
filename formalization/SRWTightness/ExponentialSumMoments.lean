import SRWTightness.ExponentialCenteredMoments
import SRWTightness.IndependentFourthSum

open MeasureTheory ProbabilityTheory

namespace SRWTightness

 theorem integrable_exponential_centered_power (k : ℕ) :
    Integrable (fun t : ℝ ↦ (t - 1) ^ k) (expMeasure 1) := by
  simp_rw [sub_eq_add_neg, add_pow]
  apply integrable_finsetSum
  intro i hi
  exact ((integrable_exponential_power i).mul_const _).mul_const _

 theorem integral_exp_product_eval {κ : Type*} [Fintype κ] (j : κ) (f : ℝ → ℝ)
    (hf : Measurable f) :
    (∫ T : κ → ℝ, f (T j) ∂Measure.pi (fun _ : κ ↦ expMeasure 1)) =
      ∫ t : ℝ, f t ∂expMeasure 1 := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hm := measurePreserving_eval (fun _ : κ ↦ expMeasure 1) j
  have he := integral_map (μ := Measure.pi (fun _ : κ ↦ expMeasure 1))
    hm.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hm.map_eq] at he
  exact he.symm

/-- The centered sum of any injectively selected family of independent Exp(1) holding times. -/
theorem exponential_selected_sum_moments {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → κ) (hj : Function.Injective j) :
    let μ := Measure.pi (fun _ : κ ↦ expMeasure 1)
    let X := fun T : κ → ℝ ↦ ∑ i : ι, (T (j i) - 1)
    (∀ k ≤ 4, Integrable (fun T ↦ X T ^ k) μ) ∧
    (∫ T, X T ∂μ) = 0 ∧
    (∫ T, X T ^ 2 ∂μ) = Fintype.card ι ∧
    (∫ T, X T ^ 4 ∂μ) = 3 * (Fintype.card ι : ℝ) ^ 2 + 6 * Fintype.card ι := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  let μ := Measure.pi (fun _ : κ ↦ expMeasure 1)
  have hInd : iIndepFun (fun i (T : κ → ℝ) ↦ T (j i) - 1) μ :=
    iIndepFun.precomp hj (iIndepFun_pi
      (X := fun _ : κ ↦ fun t : ℝ ↦ t - 1) (fun _ ↦ by fun_prop))
  have hI (i : ι) (k : ℕ) (_ : k ≤ 4) :
      Integrable (fun T : κ → ℝ ↦ (T (j i) - 1) ^ k) μ := by
    have hh := (measurePreserving_eval (fun _ : κ ↦ expMeasure 1) (j i)).integrable_comp_of_integrable
      (integrable_exponential_centered_power k)
    exact hh
  have h1 (i : ι) : (∫ T : κ → ℝ, T (j i) - 1 ∂μ) = 0 := by
    rw [integral_exp_product_eval (j i) (fun t : ℝ ↦ t - 1) (by fun_prop)]
    exact integral_exponential_centered
  have h2 (i : ι) : (∫ T : κ → ℝ, (T (j i) - 1) ^ 2 ∂μ) = 1 := by
    rw [integral_exp_product_eval (j i) (fun t : ℝ ↦ (t - 1) ^ 2) (by fun_prop)]
    exact integral_exponential_centered_two
  have h4 (i : ι) : (∫ T : κ → ℝ, (T (j i) - 1) ^ 4 ∂μ) = 9 := by
    rw [integral_exp_product_eval (j i) (fun t : ℝ ↦ (t - 1) ^ 4) (by fun_prop)]
    exact integral_exponential_centered_four
  simpa only [Finset.card_univ] using independent_centered_sum_moments μ
    (fun i (T : κ → ℝ) ↦ T (j i) - 1) (fun i ↦ by fun_prop) hInd hI h1 h2 h4 Finset.univ

end SRWTightness
