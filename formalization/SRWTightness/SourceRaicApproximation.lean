import SRWTightness.SourceWhitenedInputs
import SRWTightness.RaicWhiteningApplication

open MeasureTheory ProbabilityTheory Filter Matrix WithLp
open scoped Topology MatrixOrder

namespace SRWTightness

/-- Actual tilted source observations approximate their own Gaussian law, conditional only on Raic CLT. -/
theorem source_raic_approximation
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι) (c B P a : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hP : 0 < P) (ha : 0 < a) :
    0 < sourceLyapunovConstant c a ∧
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
        let q := u * Real.sqrt (α * (2 / Real.pi))
        let β := fun z ↦ (∑ i, b i * w i z) / q
        let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
        let F := fun i ↦ normalizedWeightedSum K k α (2 / Real.pi) u (w i)
        let μ := markProductLaw D K α k
        let ρ := μ.tilted (fun Y ↦ ∑ i, b i * F i Y)
        let Sigma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) μ
        let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
        let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
        let V : Mark K → EuclideanSpace ℝ ι :=
          fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
        let W := fun Y ↦ q⁻¹ • toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt Gamma)⁻¹) (V Y)
        (∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Sigma *ᵥ x)) →
        IsProbabilityMeasure ρ ∧ Gamma.PosDef ∧
        ∀ (s : Set (ι → ℝ)), MeasurableSet s → Convex ℝ s →
          |(ρ.map (fun Y i ↦ F i Y)).real s -
            (gaussianMeanCoordinateLaw (fun i ↦ ∫ Y, F i Y ∂ρ) Gamma).real s| ≤
            58 * sourceLyapunovConstant c a * P ^ 2 * d ^ 5 / t := by
  have hi := source_observation_whitened_inputs c B P a hc hB hP ha
  refine ⟨hi.1, ?_⟩
  filter_upwards [hi.2] with t ht
  dsimp only
  intro ι inst instDec center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  letI : Fintype ι := inst
  letI : DecidableEq ι := instDec
  have hh := ht ι center K hKD hcap hdim u hu k hk w hw hw1 b hb hlo
  obtain ⟨hprob, hGamma, hind, hmom, hsum, hcov, hthird, _, hr⟩ := hh
  letI := hprob
  refine ⟨hprob, hGamma, ?_⟩
  intro s hs hcS
  exact raic_whitened_comparison (hBE K k ι) _ k _
    (fun _ ↦ measurable_of_countable _) hind hmom hcov hthird
    _ (measurable_of_countable _) _ _ hGamma hsum _ hr s hs hcS

end SRWTightness
