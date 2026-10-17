import SRWTightness.WhitenedCovarianceGap
import SRWTightness.SourceStandardizedErrors
import SRWTightness.SourceTiltedCovariancePositive
import SRWTightness.GaussianFrobeniusEventBound

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixOrder

namespace SRWTightness

/-- Actual source tilted and untilted covariances give uniformly close centered Gaussian laws. -/
theorem source_centered_gaussian_comparison (c B P a : ℝ)
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
        let error := 2 * (Fintype.card ι * (sourceCovarianceErrorConstant c B * d ^ 3 / t) / a)
        (∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Sigma *ᵥ x)) →
        Sigma.PosDef ∧ Gamma.PosDef ∧
        (∀ (s : Set (ι → ℝ)), MeasurableSet s →
          |(gaussianCoordinateLaw Gamma).real s - (gaussianCoordinateLaw Sigma).real s| ≤ error) ∧
        (∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
          (s : Set ((ι → ℝ) × Ξ)), MeasurableSet s →
          |((gaussianCoordinateLaw Gamma).prod ν).real s -
            ((gaussianCoordinateLaw Sigma).prod ν).real s| ≤ error) := by
  obtain ⟨hC, hcov⟩ := source_observation_covariance_error c B hc hB
  have hstd := source_observation_standardized_errors c B a hc hB ha
  have hpos := source_observation_tilted_covariance_positive c B P a hc hB hP ha
  let C := sourceCovarianceErrorConstant c B
  have hlim : Tendsto (fun t : ℝ ↦ C * P *
      (sourceLowerTime (sourceLowerRadius t) ^ 4 / t)) atTop (𝓝 0) := by
    simpa using (sourceLowerTime_pow_div_t_tendsto_zero 4).const_mul (C * P)
  have hsmall := (tendsto_order.1 hlim).2 (a / 2) (by positivity)
  filter_upwards [hcov, hstd, hpos, hsmall, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hcov hstd hpos hs ht htlarge
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
  let ε := C * d ^ 3 / t
  have hstandard := hstd ι center K hKD hcap u hu k hk w hw hw1 b hb hlo
  have hSigma : Sigma.PosDef := hstandard.1
  have hGamma : Gamma.PosDef := (hpos ι center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo).2
  have hd : 0 ≤ d := (sourceLowerTime_square_upper t htlarge).1
  have hε : 0 ≤ ε := div_nonneg (mul_nonneg hC.le (pow_nonneg hd _)) ht.le
  have hentry (i j : ι) : |Gamma i j - Sigma i j| ≤ ε :=
    hcov ι center K hKD hcap u hu k hk w hw hw1 b hb i j
  have hsize : ε * Fintype.card ι ≤ a / 2 := by
    calc
      _ ≤ ε * (P * d) := mul_le_mul_of_nonneg_left hdim hε
      _ = C * P * (d ^ 4 / t) := by dsimp [ε]; ring
      _ ≤ _ := hs.le
  have hgap := whitened_covariance_lower_from_entries Sigma Gamma hSigma a ε hε hlo hentry hsize
  have hnorm := mul_le_mul_of_nonneg_left hstandard.2.2 (show (0 : ℝ) ≤ 2 by norm_num)
  refine ⟨hSigma, hGamma, ?_, ?_⟩
  · intro s hmeas
    exact (gaussian_frobenius_event_bound Sigma Gamma hSigma hGamma hgap s hmeas).trans hnorm
  · intro Ξ instΞ ν instν s hmeas
    letI : MeasurableSpace Ξ := instΞ
    letI : IsProbabilityMeasure ν := instν
    exact (gaussian_frobenius_event_bound_aux ν Sigma Gamma hSigma hGamma hgap s hmeas).trans hnorm

end SRWTightness
