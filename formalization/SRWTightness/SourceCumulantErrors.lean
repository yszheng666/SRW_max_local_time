import SRWTightness.SourceMeanError
import SRWTightness.SourceCovarianceError

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- The manuscript mean and covariance error bound for actual source-disk observations. -/
theorem source_observation_cumulant_errors (c B : ℝ) (hc : 0 < c) (hB : 0 < B) :
    0 < (sourceMeanErrorConstant c B + sourceCovarianceErrorConstant c B) ∧
    ∀ᶠ t : ℝ in atTop, ∀ (ι : Type) [Fintype ι] (center : Site) (K : Finset Site),
      let m := sourceLowerRadius t
      let D := translateFinset center (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      K ⊆ D → α * capacity D K ≤ 1 → ∀ (u : ℝ), c * t ≤ u →
      ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      ∀ (w : ι → K → ℝ), (∀ i z, 0 ≤ w i z) → (∀ i, ∑ z, w i z = 1) →
      ∀ (b : ι → ℝ), (∑ i, |b i|) ≤ B → ∀ (i j : ι),
        let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
        let μ := markProductLaw D K α k
        |(∫ Y, F i Y ∂μ.tilted (fun Y ↦ ∑ l, b l * F l Y)) -
          (∑ l, b l * covariance (F i) (F l) μ)| +
        |covariance (F i) (F j) (μ.tilted (fun Y ↦ ∑ l, b l * F l Y)) -
          covariance (F i) (F j) μ| ≤
            (sourceMeanErrorConstant c B + sourceCovarianceErrorConstant c B) *
              (sourceLowerTime m) ^ 3 / t := by
  obtain ⟨hM, hmean⟩ := source_observation_mean_error c B hc hB
  obtain ⟨hC, hcov⟩ := source_observation_covariance_error c B hc hB
  refine ⟨add_pos hM hC, ?_⟩
  filter_upwards [hmean, hcov] with t hm hv
  dsimp only
  intro ι inst center K hKD hcap u hu k hk w hw hw1 b hb i j
  letI : Fintype ι := inst
  have h1 := hm ι center K hKD hcap u hu k hk w hw hw1 b hb i
  have h2 := hv ι center K hKD hcap u hu k hk w hw hw1 b hb i j
  exact (add_le_add h1 h2).trans_eq (by ring)

end SRWTightness
