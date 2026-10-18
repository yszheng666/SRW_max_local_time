import SRWTightness.SourceUpperMarkRadius
import SRWTightness.SourceTerminalCapacityHalf

open Filter
namespace SRWTightness

/-- Actual upper-tail scales make the reference mass at most one half on every fixed-size block. -/
theorem source_upper_capacity_half (hScale : ExponentialFloorScaleInput)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (K : Finset Site),
      K ⊆ translateFinset b (diskFinset
        (c * upperTerminalFineRadius (sourceUpperLogRadius t))) →
      sourceUpperIntensity t *
        capacity (translateFinset b (diskFinset (sourceUpperMarkRadius t))) K ≤ 1 / 2 := by
  let E := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4
  have hE : 0 ≤ E := by
    have hG := diskGreenEnergyConstant_pos
    have hl : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [E]
    positivity
  obtain ⟨u₀, _, hsc⟩ := hScale c hc
  obtain ⟨B, _, hcond⟩ := source_upper_threshold_conditions hScale
  filter_upwards [sourceUpperLogRadius_eventually u₀,
    sourceUpperLogRadius_eventually (2 * (E + |Real.log c| + 1)), hcond] with t hu hlarge ht
  obtain ⟨hR, hr, hcr, hsep, _, hlogr⟩ := hsc (sourceUpperLogRadius t) hu
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  have hRup : upperTerminalRadius (sourceUpperLogRadius t) ≤ 3 * sourceUpperRadius t := by
    unfold upperTerminalRadius sourceUpperRadius
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
      (Real.exp_pos (sourceUpperLogRadius t)).le]
  have hma : 2 * (c * upperTerminalFineRadius (sourceUpperLogRadius t)) ≤
      sourceUpperRadius t := by linarith
  have hH : 0 ≤ sourceUpperBuffer t := by
    unfold sourceUpperBuffer upperTerminalFineRadius
    positivity
  have hlog : E ≤ Real.log (sourceUpperRadius t) -
      Real.log (c * upperTerminalFineRadius (sourceUpperLogRadius t)) := by
    rw [sourceUpperRadius, Real.log_exp, Real.log_mul hc.ne' (by linarith :
      upperTerminalFineRadius (sourceUpperLogRadius t) ≠ 0)]
    have hl := (abs_le.mp hlogr).2
    have hcabs := le_abs_self (Real.log c)
    have habs := abs_nonneg (Real.log c)
    linarith
  intro b K hK
  exact source_terminal_capacity_half b (sourceUpperRadius t) (sourceUpperBuffer t)
    (c * upperTerminalFineRadius (sourceUpperLogRadius t)) K hcr hma hH ht.2.2.1 hK hlog

/-- The centered terminal capacity condition follows from the actual source observation radius. -/
theorem source_upper_centered_capacity_half (hScale : ExponentialFloorScaleInput)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, ∀ K : Finset Site,
      K ⊆ diskFinset (c * upperTerminalFineRadius (sourceUpperLogRadius t)) →
      sourceUpperIntensity t * capacity (diskFinset (sourceUpperMarkRadius t)) K ≤ 1 / 2 := by
  filter_upwards [source_upper_capacity_half hScale c hc] with t ht
  intro K hK
  simpa only [translateFinset, zero_add, Finset.image_id'] using ht 0 K
    (by simpa only [translateFinset, zero_add, Finset.image_id'] using hK)

end SRWTightness
