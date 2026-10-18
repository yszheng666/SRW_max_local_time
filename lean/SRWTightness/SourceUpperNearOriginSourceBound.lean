import SRWTightness.SourceUpperNearOriginSourceEvent

open Filter MeasureTheory

namespace SRWTightness

/-- The two-zone factor is bounded by the manuscript's logarithmic-over-time factor. -/
theorem source_upper_near_origin_error_le (t : ℝ) (ht : 2 ≤ t) :
    (1 + 2 * Real.log t) / t + (1 + t) / t ^ 3 ≤ 4 * (1 + Real.log t) / t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hpoly : 1 + t ≤ 2 * t ^ 2 := by nlinarith
  have hsmall : (1 + t) / t ^ 3 ≤ 2 / t := by
    apply (div_le_div_iff₀ (pow_pos ht0 3) ht0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hpoly ht0.le]
  calc
    _ ≤ (1 + 2 * Real.log t) / t + 2 / t := add_le_add le_rfl hsmall
    _ = (3 + 2 * Real.log t) / t := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) ht0.le

/-- Source (4.35), including its quantitative height factor in the original radius parameter. -/
theorem source_upper_near_origin_source_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop, ∀ s : ℝ, 0 ≤ s →
      pathLaw.real {ω | ∃ x : Site, Real.sqrt (normSq x) ≤ R / Real.log R ∧
        Nat.ceil ((diskCenter R + s) ^ 2) ≤ localTime ω (exitSteps R ω) x} ≤
      C * Real.exp (-(2 * Real.sqrt Real.pi * s)) *
        (1 + Real.log (Real.log R)) / Real.log R := by
  obtain ⟨C, hC, hp⟩ := source_upper_near_origin_probability
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hp,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2),
    eventually_gt_atTop (0 : ℝ)] with R hp ht hR
  intro s hs
  rw [← source_upper_near_origin_event_at_radius R s hR ht]
  apply (hp s hs).trans
  have hh := mul_le_mul_of_nonneg_left (source_upper_near_origin_error_le (Real.log R) ht)
    (by positivity : 0 ≤ C * Real.exp (-(2 * Real.sqrt Real.pi * s)))
  convert hh using 1 <;> first | rfl | ring

end SRWTightness
