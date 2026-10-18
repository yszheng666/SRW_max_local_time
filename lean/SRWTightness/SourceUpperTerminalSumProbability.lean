import SRWTightness.SourceUpperConvolutionProbability
import SRWTightness.SourceUpperTerminalGaussianTail
import SRWTightness.SourceUpperTerminalResidualTail
import SRWTightness.SourceUpperGaussianMillsThreshold

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- Decreasing the common decay coefficient weakens every positive terminal-tail bound. -/
theorem source_upper_terminal_decay_mono (C r d q κ ρ : ℝ)
    (hC : 0 ≤ C) (hd : 0 < d) (hκ : κ ≤ ρ) :
    C * r ^ 2 * Real.exp (-2 * d) / d * Real.exp (-2 * q - ρ * (max q 0) ^ 2 / d) ≤
    C * r ^ 2 * Real.exp (-2 * d) / d * Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hκ (sq_nonneg (max q 0))) hd.le
  linarith only [hb]

/-- The independent Gaussian-positive-part plus residual law has the full source-scale tail. -/
theorem source_upper_terminal_sum_probability
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (c H V η B D : ℝ)
    (hc : 0 < c) (hH : 0 < H) (hV : 0 < V) (hη : 0 < η) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (a d h v q δ ε r : ℝ),
      1 ≤ d → 1 ≤ h → η * d ≤ h → η * d ≤ v → h ≤ H * d → v ≤ V * d →
      4 / η ^ 2 ≤ d → 6 * B / η ≤ d → -Real.sqrt d ≤ q →
      a = 2 * (d - h) + q + (3 / 4 : ℝ) * Real.log h + δ →
      v = d - h + ε → -B ≤ δ → ε ≤ B → 0 < r → h = Real.log r →
      (∀ z : ℝ, 0 ≤ z → ν.real (Ici z) ≤
        D * (1 + z) * Real.exp (-2 * z - c * z ^ 2 / h)) →
      ((gaussianReal 0 v.toNNReal).prod ν).real {p | a ≤ max p.1 0 + p.2} ≤
        C * r ^ 2 * Real.exp (-2 * d) / d *
          Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  obtain ⟨C₀, κ₀, hC₀, hκ₀, hG⟩ := source_upper_terminal_gaussian_tail hMills V η B hV hη hB
  obtain ⟨C₁, κ₁, hC₁, hκ₁, hR⟩ := source_upper_terminal_residual_tail c H η B hc hH hη hB
  obtain ⟨C₂, κ₂, hC₂, hκ₂, hI⟩ :=
    source_upper_terminal_convolution hIntegral c H V η B hc hH hV hη hB
  let κ := min κ₀ (min κ₁ κ₂)
  have hκ : 0 < κ := lt_min hκ₀ (lt_min hκ₁ hκ₂)
  have hκ0 : κ ≤ κ₀ := min_le_left _ _
  have hκ1 : κ ≤ κ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hκ2 : κ ≤ κ₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C₀ + D * C₁ + D * C₂, κ, by positivity, hκ, ?_⟩
  intro ν _ a d h v q δ ε r hd hh hhD hvD hhU hvU hscale herror hq
    ha hv hδ hε hr hlog hTail
  have hd0 : 0 < d := by linarith
  have hv0 : 0 < v := (mul_pos hη hd0).trans_le hvD
  have hva := source_upper_gaussian_mills_source_threshold a v d h q δ ε η B
    hη hd0 hh hvD hscale herror hq ha hv hδ hε
  have hgauss := (hG a d h v q δ ε r hd hh hhD hvD hvU hva ha hv hδ hε hr hlog).trans
    (source_upper_terminal_decay_mono C₀ r d q κ κ₀ hC₀.le hd0 hκ0)
  have hres := (hR a d h v q δ ε r hd hh hhD hvD hhU ha hv hδ hε hr hlog).trans
    (source_upper_terminal_decay_mono C₁ r d q κ κ₁ hC₁.le hd0 hκ1)
  have hint := (hI a d h v q δ ε r hd hh hhD hvD hhU hvU ha hv hδ hε hr hlog).trans
    (source_upper_terminal_decay_mono C₂ r d q κ κ₂ hC₂.le hd0 hκ2)
  have hp := source_upper_convolution_probability hConv ν a v h c D
    (hv0.trans_le hva) hv0 hTail
  have hb := add_le_add (add_le_add hgauss (mul_le_mul_of_nonneg_left hres hD))
    (mul_le_mul_of_nonneg_left hint hD)
  exact hp.trans (by convert hb using 1 <;> ring)

end SRWTightness
