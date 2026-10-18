import SRWTightness.SourceBoundedTiltApproximation
import SRWTightness.SourceCgfError

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixOrder

namespace SRWTightness

/-- The source bounded-tilt lemma: cumulant expansion, actual convex-event comparison,
auxiliary sections and superpolynomial error decay, conditional on the stated external CLT. -/
theorem source_bounded_tilt
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) (c B P a : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    0 < sourceCgfErrorConstant c B ∧ 0 < sourceTiltApproximationConstant c B P a ∧
    (∀ r : ℝ, Tendsto (fun t : ℝ ↦ sourceLowerTime (sourceLowerRadius t) ^ r *
      (sourceTiltApproximationConstant c B P a * sourceLowerTime (sourceLowerRadius t) ^ 5 / t))
      atTop (𝓝 0)) ∧
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
        |cgf (fun Y ↦ ∑ i, b i * F i Y) μ 1 -
          (∑ i, ∑ j, b i * b j * Sigma i j) / 2| ≤
            sourceCgfErrorConstant c B * d ^ 3 / t ∧
        IsProbabilityMeasure ρ ∧ Sigma.PosDef ∧ Gamma.PosDef ∧
        (∀ (s : Set (ι → ℝ)), MeasurableSet s → Convex ℝ s →
          |(ρ.map (fun Y i ↦ F i Y)).real s - (gaussianMeanCoordinateLaw target Sigma).real s| ≤ error) ∧
        (∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
          (s : Set ((ι → ℝ) × Ξ)), MeasurableSet s →
          (∀ᵐ y ∂ν, Convex ℝ ((fun x ↦ (x, y)) ⁻¹' s)) →
          |((ρ.map (fun Y i ↦ F i Y)).prod ν).real s -
            ((gaussianMeanCoordinateLaw target Sigma).prod ν).real s| ≤ error) := by
  have hcumulant := source_observation_cgf_error c B hc hB
  have happ := source_bounded_tilt_approximation hBE c B P a hc hB hP ha
  refine ⟨hcumulant.1, sourceTiltApproximationConstant_pos c B P a hc hB hP ha,
    (fun r ↦ source_tilt_approximation_scaled_tendsto_zero c B P a r hc hB hP ha), ?_⟩
  filter_upwards [hcumulant.2, happ] with t hcgf happrox
  dsimp only
  intro ι inst instDec center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  letI : Fintype ι := inst
  letI : DecidableEq ι := instDec
  exact ⟨hcgf ι center K hKD hcap u hu k hk w hw hw1 b hb,
    happrox ι center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo⟩

end SRWTightness
