import SRWTightness.SourceCenteredGaussianComparison
import SRWTightness.GaussianMeanComparison

open MeasureTheory ProbabilityTheory Filter Matrix WithLp
open scoped Topology MatrixOrder

namespace SRWTightness

/-- The actual tilted Gaussian is uniformly close to the source target Gaussian, including its mean. -/
theorem source_tilted_gaussian_comparison (c B P a : ℝ)
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
        let error := 2 * (Fintype.card ι * (sourceCovarianceErrorConstant c B * d ^ 3 / t) / a) +
          2 * (Real.sqrt (Fintype.card ι) * (sourceMeanErrorConstant c B * d ^ 3 / t) / Real.sqrt a)
        (∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Sigma *ᵥ x)) →
        Sigma.PosDef ∧ Gamma.PosDef ∧
        (∀ (s : Set (ι → ℝ)), MeasurableSet s →
          |(gaussianMeanCoordinateLaw mean Gamma).real s - (gaussianMeanCoordinateLaw target Sigma).real s| ≤ error) ∧
        (∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
          (s : Set ((ι → ℝ) × Ξ)), MeasurableSet s →
          |((gaussianMeanCoordinateLaw mean Gamma).prod ν).real s -
            ((gaussianMeanCoordinateLaw target Sigma).prod ν).real s| ≤ error) := by
  have hcov := source_centered_gaussian_comparison c B P a hc hB hP ha
  have hstd := source_observation_standardized_errors c B a hc hB ha
  filter_upwards [hcov, hstd] with t hcov hstd
  dsimp only
  intro ι inst instDec center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  letI : Fintype ι := inst
  letI : DecidableEq ι := instDec
  let m := sourceLowerRadius t
  let d := sourceLowerTime m
  let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
  let α := sourceReferenceIntensity m 14
  let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
  let μ := markProductLaw D K α k
  let ρ := μ.tilted (fun Y ↦ ∑ l, b l * F l Y)
  let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
  let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
  let mean : ι → ℝ := fun i ↦ ∫ Y, F i Y ∂ρ
  let target : ι → ℝ := fun i ↦ ∑ l, b l * Sigma i l
  let δ := 2 * (Fintype.card ι * (sourceCovarianceErrorConstant c B * d ^ 3 / t) / a)
  have hc := hcov ι center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  have hm := (hstd ι center K hKD hcap u hu k hk w hw hw1 b hb hlo).2.1
  have hmean : ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt Sigma)⁻¹) (toLp 2 (mean - target))‖ ≤
      Real.sqrt (Fintype.card ι) * (sourceMeanErrorConstant c B * d ^ 3 / t) / Real.sqrt a := hm
  have hbound := add_le_add (le_refl δ)
    (mul_le_mul_of_nonneg_left hmean (show (0 : ℝ) ≤ 2 by norm_num))
  refine ⟨hc.1, hc.2.1, ?_, ?_⟩
  · intro s hs
    exact (gaussian_mean_covariance_event_bound mean target Sigma Gamma hc.1 δ hc.2.2.1 s hs).trans hbound
  · intro Ξ instΞ ν instν s hs
    letI : MeasurableSpace Ξ := instΞ
    letI : IsProbabilityMeasure ν := instν
    exact (gaussian_mean_covariance_event_bound_aux ν mean target Sigma Gamma hc.1 δ
      (hc.2.2.2 Ξ ν) s hs).trans hbound

end SRWTightness
