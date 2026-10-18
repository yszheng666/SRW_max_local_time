import SRWTightness.SourceUpperTerminalOccupationBound
import SRWTightness.SourceUpperSmallCountOccupation
import SRWTightness.SourceUpperCapacityHalf

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

/-- Source occupation tails for every count below the coarse barrier, with capacity discharged. -/
theorem source_upper_terminal_count_bound (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (δ c a : ℝ)
    (hδ : 0 < δ) (hδone : δ < 1) (hc : 0 < c) (ha : 0 < a) :
    ∃ C κ ρ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < ρ ∧ ∀ᶠ t : ℝ in atTop,
      let D := diskFinset (sourceUpperMarkRadius t)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, normSq x ≤ ((1 - δ) * sourceUpperMarkRadius t) ^ 2) →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * r) ^ 2) →
      ∀ (K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D),
      K ⊆ diskFinset (a * r) →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ k : ℕ,
      Real.sqrt (2 * (k : ℝ)) ≤ sourceUpperTarget t s + (4 + s) + d ^ (1 / 4 : ℝ) →
      let q := sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))
      (markProductLaw D K (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      (if t - 1 ≤ Real.sqrt (2 * (k : ℝ)) then
        C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) else 0) +
        C * r ^ 2 * Real.exp (-ρ * t ^ 2 / d) := by
  obtain ⟨C₁, κ, ρ₁, hC₁, hκ, hρ₁, hlarge⟩ := source_upper_terminal_occupation_bound
    hReg hBDZ hSup hSum hMoment hConv hMills hIntegral hGreen hEmbed hScale hCount
    δ c hδ hδone hc
  obtain ⟨C₂, ρ₂, hC₂, hρ₂, hsmall⟩ := source_upper_small_count_occupation hScale hCount c hc
  obtain ⟨B, _, hcond⟩ := source_upper_threshold_conditions hScale
  refine ⟨C₁ + C₂, κ, min ρ₁ ρ₂, by positivity, hκ, lt_min hρ₁ hρ₂, ?_⟩
  filter_upwards [hlarge, hsmall, hcond, source_upper_centered_capacity_half hScale a ha,
    eventually_ge_atTop (2 : ℝ)] with t hlarge hsmall ht hcap ht2
  dsimp only
  intro A hA hcentral hdiam K hAK hKD hK s hs hslog k hku
  have hcapacity : sourceUpperIntensity t *
      capacity (diskFinset (sourceUpperMarkRadius t)) K ≤ 1 :=
    (hcap K hK).trans (by norm_num)
  have hd : 0 < upperTerminalDepth (sourceUpperLogRadius t) := by linarith [ht.2.2.2.2.2.2.1]
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let q := sourceUpperTarget t s - Real.sqrt (2 * (k : ℝ))
  let F := r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
    Real.exp (-2 * q - κ * (max q 0) ^ 2 / d)
  let G := r ^ 2 * Real.exp (-min ρ₁ ρ₂ * t ^ 2 / d)
  have hF : 0 ≤ F := by
    have hp := div_nonneg (le_max_right q 0) (Real.sqrt_nonneg d)
    dsimp [F]
    positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hexp (ρ : ℝ) (hρ : min ρ₁ ρ₂ ≤ ρ) :
      Real.exp (-ρ * t ^ 2 / d) ≤ Real.exp (-min ρ₁ ρ₂ * t ^ 2 / d) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hd.le
    exact mul_le_mul_of_nonneg_right (neg_le_neg hρ) (sq_nonneg t)
  by_cases hkl : t - 1 ≤ Real.sqrt (2 * (k : ℝ))
  · rw [if_pos hkl]
    have hk : 1 ≤ k := by
      by_contra hn
      have hk0 : k = 0 := by omega
      subst k
      norm_num at hkl
      linarith
    have hb := hlarge A hA hcentral hdiam K hAK hKD hcapacity s hs hslog k hk hkl hku
    have he := mul_le_mul_of_nonneg_left (hexp ρ₁ (min_le_left _ _))
      (show 0 ≤ C₁ * r ^ 2 by positivity)
    have hmid : (markProductLaw (diskFinset (sourceUpperMarkRadius t)) K
        (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
        C₁ * F + C₁ * G := by
      calc
        _ ≤ _ := hb.trans (add_le_add le_rfl he)
        _ = _ := by dsimp [F, G, q, d, r]; ring
    calc
      _ ≤ C₁ * F + C₁ * G := hmid
      _ ≤ (C₁ + C₂) * F + (C₁ + C₂) * G := by
        nlinarith [mul_nonneg hC₂.le hF, mul_nonneg hC₂.le hG]
      _ = _ := by dsimp [F, G, q, d, r]; ring
  · rw [if_neg hkl, zero_add]
    have hb := hsmall A hA hdiam K hAK hKD hcapacity s hs hslog k (le_of_not_ge hkl)
    have he := mul_le_mul_of_nonneg_left (hexp ρ₂ (min_le_right _ _))
      (show 0 ≤ C₂ * r ^ 2 by positivity)
    have hmid : (markProductLaw (diskFinset (sourceUpperMarkRadius t)) K
        (sourceUpperIntensity t) k).real
        {Y | ∃ z : A, sourceUpperVisitCutoff t s ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
        C₂ * G := by
      calc
        _ ≤ _ := hb.trans he
        _ = _ := by dsimp [G, d, r]; ring
    calc
      _ ≤ C₂ * G := hmid
      _ ≤ (C₁ + C₂) * G := by nlinarith [mul_nonneg hC₁.le hG]
      _ = _ := by dsimp [G, d, r]; ring

end SRWTightness
