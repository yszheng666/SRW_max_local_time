import SRWTightness.SourceTerminalWindow

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixOrder

namespace SRWTightness

/-- The actual source tilted vector comparison applies to the full continuous terminal-window event. -/
theorem source_terminal_window_approximation
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
        ∀ (τ : Type) [TopologicalSpace τ] [MeasurableSpace C(τ, ℝ)] [BorelSpace C(τ, ℝ)]
          (ν : Measure C(τ, ℝ)) [IsProbabilityMeasure ν]
          (site last : ι) (A v₀ q aStar D₀ γ : ℝ) (clock : τ → ℝ)
          (left right : τ → Option ι) (weight : τ → ℝ) (pathMean : ι → ℝ),
          let event := sourceTerminalWindow site last A v₀ q aStar D₀ γ
            clock left right weight pathMean
          |((ρ.map (fun Y i ↦ F i Y)).prod ν).real event -
            ((gaussianMeanCoordinateLaw target Sigma).prod ν).real event| ≤ error := by
  filter_upwards [source_bounded_tilt_approximation hBE c B P a hc hB hP ha] with t ht
  dsimp only
  intro ι inst instDec center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  letI : Fintype ι := inst
  letI : DecidableEq ι := instDec
  have hh := ht ι center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
  intro τ instTop instMeas instBorel ν instν site last A v₀ q aStar D₀ γ clock left right weight pathMean
  letI : TopologicalSpace τ := instTop
  letI : MeasurableSpace C(τ, ℝ) := instMeas
  letI : BorelSpace C(τ, ℝ) := instBorel
  letI : IsProbabilityMeasure ν := instν
  exact hh.2.2.2.2 C(τ, ℝ) ν _
    (sourceTerminalWindow_isClosed site last A v₀ q aStar D₀ γ
      clock left right weight pathMean).measurableSet
    (ae_of_all _ (fun path ↦ sourceTerminalWindow_section_convex
      site last A v₀ q aStar D₀ γ clock left right weight pathMean path))

end SRWTightness
