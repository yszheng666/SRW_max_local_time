import SRWTightness.SourceUpperTerminalMarkBound
import SRWTightness.SourceUpperAdmissibleThreshold
import SRWTightness.SourceUpperDiagonalVariance

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

theorem source_upper_actual_terminal_marks (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (δ c : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) :
    ∃ C κ V : ℝ, 0 < C ∧ 0 < κ ∧ 0 < V ∧ ∀ᶠ t : ℝ in atTop,
      let D := diskFinset (upperTerminalRadius (sourceUpperLogRadius t))
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * upperTerminalRadius (sourceUpperLogRadius t)) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * r) ^ 2) →
      ∀ (K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D),
      sourceUpperIntensity t * capacity D K ≤ 1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ k : ℕ, 1 ≤ k →
      t - 1 ≤ Real.sqrt (2 * (k : ℝ)) →
      Real.sqrt (2 * (k : ℝ)) ≤ sourceUpperTarget t s + (4 + s) + d ^ (1 / 4 : ℝ) →
      let q := sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))
      (markProductLaw D K (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      C * r ^ 2 * Real.exp (-2 * d) / d * Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) +
        576 * (A.card : ℝ) * Real.exp
          (-(Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ)) +
            Real.sqrt (2 * ((k : ℝ) * sourceUpperIntensity t))) ^ 2 / (2 * (V * d))) := by
  obtain ⟨C, κ, hC, hκ, ht⟩ := source_upper_terminal_mark_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale
    δ c 1 hδ hδone hc (by norm_num)
  obtain ⟨B, _, hs⟩ := source_upper_threshold_conditions hScale
  obtain ⟨V, hV, hv⟩ := source_upper_diagonal_variance hScale
  refine ⟨C, κ, V, hC, hκ, hV, ?_⟩
  filter_upwards [ht, hs, source_upper_admissible_threshold hScale, hv] with t ht hs ha hv
  dsimp only
  intro A hA hcentral hdiam K hAK hKD hcap s hs0 hslog k hk hkl hku
  obtain ⟨ht0, _, hsize, _, _, _, hd, _⟩ := hs
  obtain ⟨ε, heq, he, hadm⟩ := ha s hs0 hslog (Real.sqrt (2 * (k : ℝ))) hkl hku
  have hH : 0 ≤ sourceUpperBuffer t := by
    unfold sourceUpperBuffer upperTerminalFineRadius
    positivity
  have halpha := sourceReferenceIntensity_error (sourceUpperRadius t) (sourceUpperBuffer t)
    (Real.exp_pos _) hH hsize
  have hα : 0 ≤ sourceUpperIntensity t := by
    change 0 ≤ sourceReferenceIntensity (sourceUpperRadius t) (sourceUpperBuffer t)
    have hg : 0 < (2 / Real.pi : ℝ) := by positivity
    linarith [halpha.1]
  have hy : 0 < sourceUpperHeight t s :=
    ht0.trans_le (source_upper_height_bounds t s ht0 hs0 hslog).1
  have hcut : 1 ≤ sourceUpperVisitCutoff t s := by
    change 0 < Nat.ceil (sourceUpperHeight t s ^ 2 / Real.pi)
    exact Nat.ceil_pos.mpr (div_pos (sq_pos_of_pos hy) Real.pi_pos)
  have hb := ht A hA hcentral hdiam K hAK hKD (sourceUpperIntensity t) hα hcap
    k (sourceUpperVisitCutoff t s) hk hcut
    (sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))) ε
    (V * upperTerminalDepth (sourceUpperLogRadius t))
    (abs_le.mp he).1 hadm (mul_pos hV (by linarith))
    (fun z ↦ hv z (hKD (hAK z.property))) (by linarith [heq])
  exact hb

end SRWTightness
