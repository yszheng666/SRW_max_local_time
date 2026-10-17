import SRWTightness.SourceUpperMarkRadius
import SRWTightness.SourceUpperInteriorExactTerminal

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

theorem source_upper_padded_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (δ c : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ t : ℝ in atTop, ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * sourceUpperMarkRadius t) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤
        (c * upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2) →
      ∀ q : ℝ, -Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t)) ≤ q →
      (gaussianGreenLaw (diskFinset (sourceUpperMarkRadius t)) A).real
        {φ | ∃ x : A, 2 * upperTerminalDepth (sourceUpperLogRadius t) + q ≤
          φ x / Real.sqrt (2 / Real.pi)} ≤
        C * (upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2 *
          Real.exp (-2 * upperTerminalDepth (sourceUpperLogRadius t)) /
          upperTerminalDepth (sourceUpperLogRadius t) *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) := by
  let B := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 16
  have hB : 0 ≤ B := by
    have hE := diskGreenEnergyConstant_pos
    have hl : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [B]
    positivity
  obtain ⟨C, κ, d₀, hC, hκ, hd₀, ht⟩ := source_upper_interior_disk_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed δ B hδ hδone hB
  obtain ⟨u₀, _, hs⟩ := source_upper_terminal_scale_conditions hScale c d₀ hc hd₀
  obtain ⟨v₀, _, hg⟩ := hScale (c / δ) (div_pos hc hδ)
  obtain ⟨B₀, _, hcond⟩ := source_upper_threshold_conditions hScale
  refine ⟨C * c ^ 2, κ, by positivity, hκ, ?_⟩
  filter_upwards [sourceUpperLogRadius_eventually u₀, sourceUpperLogRadius_eventually v₀,
    hcond] with t hu hv hcond
  intro A hA hcentral hdiam q hq
  obtain ⟨_, hr, _, hd, hhL, hhU⟩ := hs (sourceUpperLogRadius t) hu
  obtain ⟨_, _, _, hsep, _, _⟩ := hg (sourceUpperLogRadius t) hv
  have hm := mul_le_mul_of_nonneg_left hsep hδ.le
  have he : δ * (64 * ((c / δ) * upperTerminalFineRadius (sourceUpperLogRadius t))) =
      64 * (c * upperTerminalFineRadius (sourceUpperLogRadius t)) := by
    field_simp
    <;> ring
  rw [he] at hm
  have hsize := hcond.2.2.1
  have hR := (source_upper_mark_radius_bounds t hsize).2.1
  have hδR := mul_le_mul_of_nonneg_left hR hδ.le
  have hsep' : 32 * (c * upperTerminalFineRadius (sourceUpperLogRadius t)) ≤
      δ * sourceUpperMarkRadius t := by linarith
  have hb := ht (sourceUpperMarkRadius t) (c * upperTerminalFineRadius (sourceUpperLogRadius t))
    (upperTerminalDepth (sourceUpperLogRadius t)) q A hr hsep' hA hcentral hdiam hd
    (source_upper_mark_radius_depth_error t hsize) hhL hhU hq
  calc
    _ ≤ C * (c * upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2 *
        Real.exp (-2 * upperTerminalDepth (sourceUpperLogRadius t)) /
        upperTerminalDepth (sourceUpperLogRadius t) *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) := hb
    _ = _ := by ring

end SRWTightness
