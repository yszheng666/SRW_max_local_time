import SRWTightness.SourceGWTubeUpper
import SRWTightness.SourceTerminalWindowSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace SRWTightness

/-- Upper endpoint of the lower GW tube in the source one-point application. -/
noncomputable def sourceGWLowerEndpoint (t : ℝ) : ℝ :=
  4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) -
    2 * sourceLowerTime (sourceLowerRadius t) ^ (2 / 5 : ℝ)

/-- The source curvature correction is eventually small compared with the deficit scale. -/
theorem source_gw_curvature_small :
    ∀ᶠ t : ℝ in atTop,
      2 * sourceLowerTime (sourceLowerRadius t) ^ (2 / 5 : ℝ) ≤
        Real.sqrt (sourceLowerTime (sourceLowerRadius t)) / 2 := by
  have hdlim : Tendsto (fun t : ℝ ↦ sourceLowerTime (sourceLowerRadius t)) atTop atTop :=
    tendsto_atTop.2 (fun D ↦ source_lower_time_eventually_ge D)
  have hlim := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hdlim
  have hh := (tendsto_order.1 hlim).2 (1 / 4 : ℝ) (by norm_num)
  filter_upwards [source_lower_time_eventually_ge 1, hh] with t hd hh
  have hd0 : 0 < sourceLowerTime (sourceLowerRadius t) := by linarith
  have he : sourceLowerTime (sourceLowerRadius t) ^ (2 / 5 : ℝ) /
      Real.sqrt (sourceLowerTime (sourceLowerRadius t)) =
      sourceLowerTime (sourceLowerRadius t) ^ (-(1 / 10 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hd0]
    norm_num
  dsimp only [Function.comp_def] at hh
  rw [← he] at hh
  have hmul := (div_lt_iff₀ (Real.sqrt_pos.mpr hd0)).mp hh
  linarith

/-- Both endpoint margins of the source lower tube are ordered and have the required size. -/
theorem source_gw_endpoint_margins :
    ∀ᶠ t : ℝ in atTop, ∀ q : ℝ,
      Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
      let y := sourceTerminalRoot t q + 1 / 4
      let b := sourceGWLowerEndpoint t
      y ≤ b ∧ q / 2 ≤ b - y ∧ b - y ≤ q + 4 ∧
        (1 + 4 - Real.sqrt 2) * (1 + b - y) ≤
          4 * (sourceCoarseGeneration t : ℝ) := by
  filter_upwards [source_gw_curvature_small, source_deficit_large_conditions,
    source_lower_time_eventually_ge 4] with t hcurve ht hd
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  have hT := sourceTotalTime_ge_half t ht htE
  unfold sourceTotalTime at hT
  have hN : 5 * sourceLowerTime (sourceLowerRadius t) ≤
      (sourceCoarseGeneration t : ℝ) := by linarith
  intro q hql hqu
  dsimp only
  have hs0 := Real.sqrt_nonneg (sourceLowerTime (sourceLowerRadius t))
  have hs := Real.sq_sqrt (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith)
  have hsd : Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤
      sourceLowerTime (sourceLowerRadius t) := by nlinarith
  have hp0 := Real.rpow_nonneg
    (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith) (2 / 5 : ℝ)
  have he : sourceGWLowerEndpoint t - (sourceTerminalRoot t q + 1 / 4) =
      15 / 4 + q - 2 * sourceLowerTime (sourceLowerRadius t) ^ (2 / 5 : ℝ) := by
    unfold sourceGWLowerEndpoint sourceTerminalRoot
    ring
  have hlo : q / 2 ≤ sourceGWLowerEndpoint t - (sourceTerminalRoot t q + 1 / 4) := by
    rw [he]
    linarith
  have hhi : sourceGWLowerEndpoint t - (sourceTerminalRoot t q + 1 / 4) ≤ q + 4 := by
    rw [he]
    linarith
  refine ⟨by linarith, hlo, hhi, ?_⟩
  have hsqrt2 := Real.sqrt_nonneg (2 : ℝ)
  have hmargin : 0 ≤ 1 + sourceGWLowerEndpoint t - (sourceTerminalRoot t q + 1 / 4) := by
    linarith
  have hbound : 1 + sourceGWLowerEndpoint t - (sourceTerminalRoot t q + 1 / 4) ≤
      4 * sourceLowerTime (sourceLowerRadius t) := by
    nlinarith
  nlinarith [mul_nonneg hsqrt2 hmargin]

end SRWTightness
