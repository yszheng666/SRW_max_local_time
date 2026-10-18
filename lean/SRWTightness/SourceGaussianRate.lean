import SRWTightness.SourceTiltedGaussianComparison
import SRWTightness.GaussianComparisonRate

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixOrder

namespace SRWTightness

noncomputable def sourceGaussianComparisonConstant (c B P a : ℝ) : ℝ :=
  2 * P * sourceCovarianceErrorConstant c B / a +
    2 * P * sourceMeanErrorConstant c B / Real.sqrt a

/-- The uniform Gaussian comparison constant is positive in the source parameter range. -/
theorem sourceGaussianComparisonConstant_pos (c B P a : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    0 < sourceGaussianComparisonConstant c B P a := by
  have hC := (source_observation_covariance_error c B hc hB).1
  have hM := (source_observation_mean_error c B hc hB).1
  unfold sourceGaussianComparisonConstant
  positivity

/-- The complete source Gaussian comparison has the uniform d^5/t rate. -/
theorem source_gaussian_comparison_rate (c B P a : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    ∀ᶠ t : ℝ in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (center : Site) (K : Finset Site),
      let m := sourceLowerRadius t
      let d := sourceLowerTime m
      let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      K ⊆ D → α * capacity D K ≤ 1 → (Fintype.card ι : ℝ) ≤ P * d →
      ∀ (u : ℝ), c * t ≤ u → ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      ∀ (w : ι → K → ℝ), (∀ i z, 0 ≤ w i z) → (∀ i, ∑ z, w i z = 1) →
      ∀ (b : ι → ℝ), (∑ i, |b i|) ≤ B →
        let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
        let μ := markProductLaw D K α k
        let ρ := μ.tilted (fun Y ↦ ∑ l, b l * F l Y)
        let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
        let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
        let mean : ι → ℝ := fun i ↦ ∫ Y, F i Y ∂ρ
        let target : ι → ℝ := fun i ↦ ∑ l, b l * Sigma i l
        let error := sourceGaussianComparisonConstant c B P a * d ^ 5 / t
        (∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Sigma *ᵥ x)) →
        Sigma.PosDef ∧ Gamma.PosDef ∧
        (∀ (s : Set (ι → ℝ)), MeasurableSet s →
          |(gaussianMeanCoordinateLaw mean Gamma).real s - (gaussianMeanCoordinateLaw target Sigma).real s| ≤ error) ∧
        (∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
          (s : Set ((ι → ℝ) × Ξ)), MeasurableSet s →
          |((gaussianMeanCoordinateLaw mean Gamma).prod ν).real s -
            ((gaussianMeanCoordinateLaw target Sigma).prod ν).real s| ≤ error) := by
  have hgauss := source_tilted_gaussian_comparison c B P a hc hB hP ha
  have hC := (source_observation_covariance_error c B hc hB).1
  have hM := (source_observation_mean_error c B hc hB).1
  filter_upwards [hgauss, eventually_ge_atTop (sourceScaleThreshold 4)] with t hg ht
  dsimp only
  intro ι inst instDec center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  letI : Fintype ι := inst
  letI : DecidableEq ι := instDec
  have hh := hg ι center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  have hd := sourceLowerTime_ge_one t ht
  have ht0 : 0 ≤ t := by
    have hh := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    linarith
  have hr := gaussian_comparison_rate_bound (Fintype.card ι)
    (sourceCovarianceErrorConstant c B) (sourceMeanErrorConstant c B) P a
    (sourceLowerTime (sourceLowerRadius t)) t hC.le hM.le hP.le ha hd ht0 hdim
  refine ⟨hh.1, hh.2.1, ?_, ?_⟩
  · intro s hs
    exact (hh.2.2.1 s hs).trans hr
  · intro Ξ instΞ ν instν s hs
    letI : MeasurableSpace Ξ := instΞ
    letI : IsProbabilityMeasure ν := instν
    exact (hh.2.2.2 Ξ ν s hs).trans hr

/-- The source Gaussian error vanishes after multiplication by every fixed real power of d. -/
theorem source_gaussian_error_scaled_tendsto_zero (c B P a r : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    Tendsto (fun t : ℝ ↦ sourceLowerTime (sourceLowerRadius t) ^ r *
      (sourceGaussianComparisonConstant c B P a *
        sourceLowerTime (sourceLowerRadius t) ^ 5 / t)) atTop (𝓝 0) := by
  exact source_normal_error_scaled_tendsto_zero _ r
    (sourceGaussianComparisonConstant_pos c B P a hc hB hP ha).le

end SRWTightness
