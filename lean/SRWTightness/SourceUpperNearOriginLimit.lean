import SRWTightness.SourceUpperNearOriginProbability
import SRWTightness.LogPowerDomination

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

/-- The two-zone spatial factor vanishes at infinity. -/
theorem source_upper_near_origin_error_vanishes :
    Tendsto (fun t : ℝ ↦ (1 + 2 * Real.log t) / t + (1 + t) / t ^ 3)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hl : Tendsto (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 1)).tendsto_div_nhds_zero
  have hh : Tendsto (fun t : ℝ ↦ (t⁻¹ + 2 * (Real.log t / t)) +
      ((t⁻¹) ^ 3 + (t⁻¹) ^ 2)) atTop (𝓝 0) := by
    simpa using (hi.add (hl.const_mul 2)).add ((hi.pow 3).add (hi.pow 2))
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  field_simp
  <;> ring

/-- The actual near-origin high-point probability vanishes at every fixed nonnegative height. -/
theorem source_upper_near_origin_vanishes (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun t : ℝ ↦ pathLaw.real (sourceUpperNearOriginHighEvent t s))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, ht⟩ := source_upper_near_origin_probability
  have hh := source_upper_near_origin_error_vanishes.const_mul
    (C * Real.exp (-(2 * Real.sqrt Real.pi * s)))
  simp only [mul_zero] at hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hh
  filter_upwards [ht] with t ht
  exact ht s hs

/-- The same actual near-origin probability vanishes in the manuscript outer-radius parameter. -/
theorem source_upper_near_origin_radius_vanishes (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun R : ℝ ↦ pathLaw.real (sourceUpperNearOriginHighEvent (Real.log R) s))
      atTop (𝓝 0) :=
  (source_upper_near_origin_vanishes s hs).comp Real.tendsto_log_atTop

end SRWTightness
