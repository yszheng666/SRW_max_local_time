import SRWTightness.SourceUpperPaddedPerturbedTerminal
import SRWTightness.ProjectedMarkNormalizedBranches
import SRWTightness.GaussianNegativeUniformTail

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

theorem source_upper_padded_terminal_mark_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (δ c E : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) (hE : 0 ≤ E) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ t : ℝ in atTop,
      let u := sourceUpperLogRadius t
      let D := diskFinset (sourceUpperMarkRadius t)
      let d := upperTerminalDepth u
      let r := upperTerminalFineRadius u
      let g : ℝ := 2 / Real.pi
      ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * sourceUpperMarkRadius t) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * r) ^ 2) →
      ∀ (K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D) (α : ℝ),
      0 ≤ α → α * capacity D K ≤ 1 → ∀ (k a : ℕ), 1 ≤ k → 1 ≤ a →
      ∀ q ε V : ℝ, -E ≤ ε → -Real.sqrt d ≤ q + ε → 0 < V →
      (∀ z : A, killedGreen D z z ≤ V) →
      Real.sqrt (2 * (a : ℝ) / g) - Real.sqrt (α / g) * Real.sqrt (2 * (k : ℝ)) =
        2 * d + (q + ε) →
      (markProductLaw D K α k).real
        {Y | ∃ z : A, a ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      C * r ^ 2 * Real.exp (-2 * d) / d * Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) +
        576 * (A.card : ℝ) * Real.exp
          (-(Real.sqrt (2 * (a : ℝ)) + Real.sqrt (2 * ((k : ℝ) * α))) ^ 2 / (2 * V)) := by
  obtain ⟨C, κ, hC, hκ, ht⟩ := source_upper_padded_perturbed_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale
      δ c E hδ hδone hc hE
  refine ⟨576 * C, κ, by positivity, hκ, ?_⟩
  filter_upwards [ht] with t ht
  dsimp only
  intro A hA hcentral hdiam K hAK hKD α hα hcap k a hk ha q ε V hε hq hV hdiag heq
  have hp := ht A hA hcentral hdiam q ε hε hq
  have hb := projected_fixed_mark_normalized_branches
    (diskFinset (sourceUpperMarkRadius t)) A K hAK hKD α
    (2 / Real.pi) hα (by positivity) hcap k a hk ha
  rw [heq] at hb
  have hn := gaussian_negative_tail_sum_uniform
    (diskFinset (sourceUpperMarkRadius t)) A (hAK.trans hKD)
    (Real.sqrt (2 * (a : ℝ)) + Real.sqrt (2 * ((k : ℝ) * α))) V
    (by positivity) hV hdiag
  have hm := mul_le_mul_of_nonneg_left (add_le_add hp hn) (by norm_num : (0 : ℝ) ≤ 576)
  exact hb.trans (by convert hm using 1 <;> ring)

end SRWTightness
