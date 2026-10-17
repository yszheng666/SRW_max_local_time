import SRWTightness.SourceRaicApproximation
import SRWTightness.SourceGaussianRate

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixOrder

namespace SRWTightness

noncomputable def sourceTiltApproximationConstant (c B P a : ℝ) : ℝ :=
  58 * sourceLyapunovConstant c a * P ^ 2 + sourceGaussianComparisonConstant c B P a

theorem sourceTiltApproximationConstant_pos (c B P a : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    0 < sourceTiltApproximationConstant c B P a := by
  have hl := (source_observation_whitened_inputs c B P a hc hB hP ha).1
  have hg := sourceGaussianComparisonConstant_pos c B P a hc hB hP ha
  unfold sourceTiltApproximationConstant
  positivity

/-- Source (6.13), including convex auxiliary sections, conditional on the external Raic theorem. -/
theorem source_bounded_tilt_approximation
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) (c B P a : ℝ)
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
        let error := sourceTiltApproximationConstant c B P a * d ^ 5 / t
        (∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Sigma *ᵥ x)) →
        IsProbabilityMeasure ρ ∧ Sigma.PosDef ∧ Gamma.PosDef ∧
        (∀ (s : Set (ι → ℝ)), MeasurableSet s → Convex ℝ s →
          |(ρ.map (fun Y i ↦ F i Y)).real s - (gaussianMeanCoordinateLaw target Sigma).real s| ≤ error) ∧
        (∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
          (s : Set ((ι → ℝ) × Ξ)), MeasurableSet s →
          (∀ᵐ y ∂ν, Convex ℝ ((fun x ↦ (x, y)) ⁻¹' s)) →
          |((ρ.map (fun Y i ↦ F i Y)).prod ν).real s -
            ((gaussianMeanCoordinateLaw target Sigma).prod ν).real s| ≤ error) := by
  have hb := (source_raic_approximation hBE c B P a hc hB hP ha).2
  have hg := source_gaussian_comparison_rate c B P a hc hB hP ha
  filter_upwards [hb, hg] with t hb hg
  dsimp only
  intro ι inst instDec center K hKD hcap hdim u hu k hk w hw hw1 b hbn hlo
  letI : Fintype ι := inst
  letI : DecidableEq ι := instDec
  have hclt := hb ι center K hKD hcap hdim u hu k hk w hw hw1 b hbn hlo
  have hgauss := hg ι center K hKD hcap hdim u hu k hk w hw hw1 b hbn hlo
  letI := hclt.1
  let d := sourceLowerTime (sourceLowerRadius t)
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
  let μ := markProductLaw (translateFinset center
    (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K α k
  let ρ := μ.tilted (fun Y ↦ ∑ l, b l * F l Y)
  let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
  let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
  let mean := fun i ↦ ∫ Y, F i Y ∂ρ
  let target := fun i ↦ ∑ l, b l * Sigma i l
  have hbound (s : Set (ι → ℝ)) (hs : MeasurableSet s) (hcs : Convex ℝ s) :
      |(ρ.map (fun Y i ↦ F i Y)).real s -
        (gaussianMeanCoordinateLaw target Sigma).real s| ≤
        sourceTiltApproximationConstant c B P a * d ^ 5 / t := by
    have h1 := hclt.2.2 s hs hcs
    have h2 := hgauss.2.2.1 s hs
    calc
      _ ≤ |(ρ.map (fun Y i ↦ F i Y)).real s -
            (gaussianMeanCoordinateLaw mean Gamma).real s| +
          |(gaussianMeanCoordinateLaw mean Gamma).real s -
            (gaussianMeanCoordinateLaw target Sigma).real s| := abs_sub_le _ _ _
      _ ≤ 58 * sourceLyapunovConstant c a * P ^ 2 * d ^ 5 / t +
          sourceGaussianComparisonConstant c B P a * d ^ 5 / t := add_le_add h1 h2
      _ = _ := by unfold sourceTiltApproximationConstant; ring
  refine ⟨hclt.1, hgauss.1, hgauss.2.1, hbound, ?_⟩
  intro Ξ instΞ ν instν s hs hcs
  letI : MeasurableSpace Ξ := instΞ
  letI : IsProbabilityMeasure ν := instν
  have hF : Measurable (fun Y i ↦ F i Y) := measurable_of_countable _
  letI : IsProbabilityMeasure (ρ.map (fun Y i ↦ F i Y)) :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  letI := gaussianMeanCoordinateLaw_isProbabilityMeasure target Sigma
  exact convex_event_comparison_aux _ _ ν _ hbound s hs hcs

/-- The full source approximation error decays faster than every fixed inverse power of d. -/
theorem source_tilt_approximation_scaled_tendsto_zero (c B P a r : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    Tendsto (fun t : ℝ ↦ sourceLowerTime (sourceLowerRadius t) ^ r *
      (sourceTiltApproximationConstant c B P a *
        sourceLowerTime (sourceLowerRadius t) ^ 5 / t)) atTop (𝓝 0) :=
  source_normal_error_scaled_tendsto_zero _ r
    (sourceTiltApproximationConstant_pos c B P a hc hB hP ha).le

end SRWTightness
