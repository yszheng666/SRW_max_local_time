import SRWTightness.SourceUpperInteriorDiskGreenTerminal
import SRWTightness.SourceUpperTerminalScaleConditions

open MeasureTheory ProbabilityTheory
namespace SRWTightness

theorem source_upper_interior_exact_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (δ c : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) :
    ∃ C κ u₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u → ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * upperTerminalRadius u) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * upperTerminalFineRadius u) ^ 2) →
      ∀ q : ℝ, -Real.sqrt (upperTerminalDepth u) ≤ q →
      (gaussianGreenLaw (diskFinset (upperTerminalRadius u)) A).real
        {φ | ∃ x : A, 2 * upperTerminalDepth u + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        C * (upperTerminalFineRadius u) ^ 2 * Real.exp (-2 * upperTerminalDepth u) /
          upperTerminalDepth u *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / upperTerminalDepth u) := by
  obtain ⟨C, κ, d₀, hC, hκ, hd₀, ht⟩ := source_upper_interior_disk_green_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed δ hδ hδone
  obtain ⟨u₀, hu₀, hs⟩ := source_upper_terminal_scale_conditions hScale c d₀ hc hd₀
  obtain ⟨v₀, hv₀, hg⟩ := hScale (c / δ) (div_pos hc hδ)
  refine ⟨C * c ^ 2, κ, max u₀ v₀, by positivity, hκ,
    hu₀.trans_le (le_max_left _ _), ?_⟩
  intro u hu A hA hcentral hdiam q hq
  obtain ⟨hR, hr, hsep, hd, hhL, hhU⟩ := hs u ((le_max_left _ _).trans hu)
  obtain ⟨_, _, _, hgsep, _, _⟩ := hg u ((le_max_right _ _).trans hu)
  have hm := mul_le_mul_of_nonneg_left hgsep hδ.le
  have he : δ * (64 * ((c / δ) * upperTerminalFineRadius u)) =
      64 * (c * upperTerminalFineRadius u) := by
    field_simp
    <;> ring
  rw [he] at hm
  have hsep' : 32 * (c * upperTerminalFineRadius u) ≤ δ * upperTerminalRadius u := by
    linarith
  have hb := ht (upperTerminalRadius u) (c * upperTerminalFineRadius u)
    (upperTerminalDepth u) q A hR hr hsep' hA hcentral hdiam hd rfl hhL hhU hq
  calc
    _ ≤ C * (c * upperTerminalFineRadius u) ^ 2 * Real.exp (-2 * upperTerminalDepth u) /
        upperTerminalDepth u *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / upperTerminalDepth u) := hb
    _ = _ := by ring

end SRWTightness
