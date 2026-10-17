import SRWTightness.SourceUpperEmbeddedShiftedTerminal
import SRWTightness.ExternalBufferedInteriorDiskEmbedding
import SRWTightness.DiskTerminalScaleTransfer

open MeasureTheory ProbabilityTheory
namespace SRWTightness

theorem source_upper_interior_disk_terminal (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (δ B : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hB : 0 ≤ B) :
    ∃ C κ d₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < d₀ ∧
      ∀ (R r d q : ℝ) (A : Finset Site), 1 ≤ r → 32 * r ≤ δ * R → A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * R) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ r ^ 2) →
      d₀ ≤ d → |d - Real.log R| ≤ B →
      d / 8 ≤ Real.log r → Real.log r + Real.log 64 ≤ d / 2 →
      -Real.sqrt d ≤ q →
      (gaussianGreenLaw (diskFinset R) A).real
        {φ | ∃ x : A, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  classical
  have hlog16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨C, κ, d₀, hC, hκ, hd₀, ht⟩ := source_upper_embedded_shifted_terminal
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen
      (1 / 16) (B + Real.log 16) (by norm_num) (by norm_num) (add_nonneg hB hlog16)
  refine ⟨4096 * C, κ, d₀, by positivity, hκ, hd₀, ?_⟩
  intro R r d q A hr hRr hA hcentral hdiam hd herr hhL hhU hq
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := by
    have hp : 0 < δ * R := by linarith
    exact (mul_pos_iff_of_pos_left hδ).mp hp
  have hd0 : 0 < d := hd₀.trans_le hd
  obtain ⟨a, b, m, n, hn, hnm, hAE, hEK, hKD, hrl, hru, hRl, hRu, hfbuf, hob⟩ :=
    hEmbed δ R r A hδ hδone hr hRr hA hcentral hdiam
  let E := latticeSquareInterior a (2 ^ n)
  let D := latticeSquareInterior b (2 ^ m)
  let f : A ↪ E := ⟨fun x ↦ ⟨x.val, hAE x.property⟩, by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : E ↦ z.val) hxy)⟩
  let J : Finset E := Finset.univ.map f
  obtain ⟨z, hz⟩ := hA
  let o : E := f ⟨z, hz⟩
  have ho : o ∈ J := Finset.mem_map.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩
  have hf : ∀ x ∈ J, squareProportionalBuffer (1 / 16) a (2 ^ n) x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hfbuf y.val y.property
  have hg : ∀ x ∈ J, squareProportionalBuffer (1 / 16) b (2 ^ m) x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hob y.val y.property
  have hs := terminal_fine_log_proportions d r ((2 : ℝ) ^ n) hr0 hrl hru hhL hhU
  have he := terminal_outer_log_error R ((2 : ℝ) ^ m) d B hR0 hRl hRu herr
  have hb := ht D (diskFinset R) E a b m n rfl rfl hn hnm hEK hKD o J d
    (Real.log ((2 : ℝ) ^ n)) q ((2 : ℝ) ^ n) ho rfl rfl hd he hf hg hs.1 hs.2 hq
  have hσ : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hp := gaussian_selected_observation_probability (diskFinset R) A E hAE hEK
    Finset.univ ((2 * d + q) * Real.sqrt (2 / Real.pi))
  have hevent : {φ : EuclideanSpace ℝ E | ∃ x ∈ (Finset.univ : Finset A),
      (2 * d + q) * Real.sqrt (2 / Real.pi) ≤ φ ⟨x.val, hAE x.property⟩} =
      {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} := by
    ext φ
    constructor
    · rintro ⟨x, hx, ht⟩
      exact ⟨f x, Finset.mem_map.mpr ⟨x, hx, rfl⟩, (le_div_iff₀ hσ).mpr ht⟩
    · rintro ⟨y, hy, ht⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact ⟨x, hx, (le_div_iff₀ hσ).mp ht⟩
  rw [hevent] at hp
  have hp' : (gaussianGreenLaw (diskFinset R) A).real
      {φ | ∃ x : A, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} =
      (gaussianGreenLaw (diskFinset R) E).real
        {φ | ∃ x ∈ J, 2 * d + q ≤ φ x / Real.sqrt (2 / Real.pi)} := by
    simpa only [upperExceedanceOn, Finset.mem_univ, true_and, le_div_iff₀ hσ] using hp
  rw [hp']
  refine hb.trans ?_
  have hsq : ((2 : ℝ) ^ n) ^ 2 ≤ 4096 * r ^ 2 := by
    have hp0 : 0 ≤ (2 : ℝ) ^ n := by positivity
    nlinarith
  calc
    _ = ((2 : ℝ) ^ n) ^ 2 * (C * Real.exp (-2 * d) / d *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d)) := by ring
    _ ≤ (4096 * r ^ 2) * (C * Real.exp (-2 * d) / d *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d)) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = _ := by ring

end SRWTightness
