import SRWTightness.NormalizedMeanError
import SRWTightness.ObservationCovarianceCgf

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Entrywise tilted mean error against the actual covariance matrix times the signed tilt. -/
theorem observationFamily_mean_error {ι : Type*} [Fintype ι]
    (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1)
    (w : ι → K → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (b : ι → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ i, |b i|) < (u * Real.sqrt (α * g)) / (8 * L))
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (i : ι) :
    let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
    let μ := markProductLaw D K α k
    |(∫ Y, F i Y ∂μ.tilted (fun Y ↦ ∑ l, b l * F l Y)) -
      (∑ l, b l * covariance (F i) (F l) μ)| ≤
        35389464 * L ^ 3 * (∑ l, |b l|) ^ 2 /
          (2 * u * (Real.sqrt (α * g)) ^ 3) := by
  letI := markProductLaw_isProbabilityMeasure D K α hα.le hcap k
  let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
  let μ := markProductLaw D K α k
  let v := fun z ↦ ∑ l, b l * w l z
  let c := u * Real.sqrt (α * g)
  have hc : 0 < c := by dsimp [c]; positivity
  have hv : (∑ z, |v z / c|) ≤ (∑ l, |b l|) / c :=
    normalized_observation_coefficients_l1 w hw hw1 b c hc
  have hs : (∑ z, |v z / c|) < 1 / (8 * L) := by
    apply hv.trans_lt
    apply (div_lt_iff₀ hc).mpr
    simpa only [c, one_div, div_eq_mul_inv, mul_comm, one_mul] using hsmall
  have hF (l : ι) : MemLp (F l) 2 μ :=
    normalizedWeightedSum_memLp_two D K α g u hα.le hcap k (w l)
  have hcov : covariance (F i) (fun Y ↦ ∑ l, b l * F l Y) μ =
      ∑ l, b l * covariance (F i) (F l) μ := by
    rw [covariance_fun_sum_right (fun l ↦ (hF l).const_mul (b l)) (hF i)]
    simp only [covariance_const_mul_right]
  have hf : (fun Y : MarkSamples K k ↦ ∑ l, b l * F l Y) =
      normalizedWeightedSum K k α g u v := by
    funext Y
    exact observation_linear_combination w b (fun z ↦ normalizedMarkSum K k α g u z Y)
  change |(∫ Y, F i Y ∂μ.tilted (fun Y ↦ ∑ l, b l * F l Y)) -
    (∑ l, b l * covariance (F i) (F l) μ)| ≤ _
  rw [← hcov, hf]
  have hh := normalizedWeightedSum_mean_error D K hKD α g u hα hg hu hcap
    (w i) (hw i) (hw1 i) v L hL hαL hG hs k
  refine hh.trans ?_
  calc
    _ ≤ k * (35389464 * L ^ 3 * (((∑ l, |b l|) / c) ^ 2)) / c := by
      apply div_le_div_of_nonneg_right _ hc.le
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) hv 2
    _ = _ := by
      rw [← hk]
      dsimp [c]
      have hr : Real.sqrt (α * g) ≠ 0 := ne_of_gt (by positivity)
      field_simp
      <;> ring

end SRWTightness
