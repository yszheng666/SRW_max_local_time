import SRWTightness.SourceUpperPaddedActualTerminalMarks
import SRWTightness.SourceUpperNegativeBranch
import SRWTightness.LatticeDiameterCount

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

theorem source_upper_terminal_occupation_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (δ c : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) :
    ∃ C κ ρ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ρ ∧ ∀ᶠ t : ℝ in atTop,
      let D := diskFinset (sourceUpperMarkRadius t)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * sourceUpperMarkRadius t) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * r) ^ 2) →
      ∀ (K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D),
      sourceUpperIntensity t * capacity D K ≤ 1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ k : ℕ, 1 ≤ k →
      t - 1 ≤ Real.sqrt (2 * (k : ℝ)) →
      Real.sqrt (2 * (k : ℝ)) ≤ sourceUpperTarget t s + (4 + s) + d ^ (1 / 4 : ℝ) →
      let q := sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))
      (markProductLaw D K (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) +
        C * r ^ 2 * Real.exp (-ρ * t ^ 2 / d) := by
  obtain ⟨C, κ, V, hC, hκ, hV, ht⟩ := source_upper_padded_actual_terminal_marks
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale δ c hδ hδone hc
  obtain ⟨K₀, hK₀, hcount⟩ := lattice_diameter_count hCount c hc
  obtain ⟨B, _, hs⟩ := source_upper_threshold_conditions hScale
  refine ⟨C + 576 * K₀, κ, (2 / Real.pi) / (2 * V), by positivity, hκ, by positivity, ?_⟩
  filter_upwards [ht, hs] with t ht hs
  dsimp only
  intro A hA hcentral hdiam K hAK hKD hcap s hs0 hslog k hk hkl hku
  obtain ⟨ht0, _, _, _, _, hr, hd, _⟩ := hs
  have hd0 : 0 < upperTerminalDepth (sourceUpperLogRadius t) := by linarith
  have hb := ht A hA hcentral hdiam K hAK hKD hcap s hs0 hslog k hk hkl hku
  have hcard := hcount (upperTerminalFineRadius (sourceUpperLogRadius t)) hr A hA hdiam
  have he := source_upper_negative_branch_exponential t s (sourceUpperIntensity t) V
    (upperTerminalDepth (sourceUpperLogRadius t)) k ht0 hs0 hslog hV hd0
  have hn := mul_le_mul
    (mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 576)) he
    (Real.exp_pos _).le (by positivity : 0 ≤ 576 *
      (K₀ * upperTerminalFineRadius (sourceUpperLogRadius t) ^ 2))
  let q := sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let F := r ^ 2 * Real.exp (-2 * d) / d * Real.exp (-2 * q - κ * (max q 0) ^ 2 / d)
  let G := r ^ 2 * Real.exp (-((2 / Real.pi) / (2 * V)) * t ^ 2 / d)
  have hF : 0 ≤ F := by dsimp [F, d]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hp : 0 ≤ max q 0 / Real.sqrt d :=
    div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  have hcost : C * F + (576 * K₀) * G ≤
      (C + 576 * K₀) * F * (1 + max q 0 / Real.sqrt d) + (C + 576 * K₀) * G := by
    have h1 := mul_nonneg (show 0 ≤ 576 * K₀ by positivity) hF
    have h2 := mul_nonneg hC.le hG
    have h3 := mul_nonneg (mul_nonneg (show 0 ≤ C + 576 * K₀ by positivity) hF) hp
    nlinarith
  have hsum := hb.trans (add_le_add le_rfl hn)
  have hmiddle :
      (markProductLaw (diskFinset (sourceUpperMarkRadius t)) K (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      C * F + (576 * K₀) * G := by
    calc
      _ ≤ _ := hsum
      _ = _ := by dsimp [F, G, q, d, r]; ring
  refine hmiddle.trans ?_
  calc
    _ ≤ _ := hcost
    _ = _ := by dsimp [F, G, q, d, r]; ring

end SRWTightness
