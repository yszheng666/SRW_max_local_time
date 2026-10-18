import SRWTightness.SourceTerminalEnergy

namespace SRWTightness

noncomputable def sourceDiscreteError (b : Site) (m a H : ℝ) : ℝ :=
  equilibriumDiscreteError (translateFinset b (diskFinset (Real.exp 1 * m + H)))
    (translateFinset b (diskFinset a)) (2 / Real.pi)

theorem sourceDiscreteError_radius_upper (b : Site) (m a H : ℝ)
    (ha : 4 ≤ a) (hma : 2 * a ≤ m) (hH : 0 ≤ H) :
    sourceDiscreteError b m a H ≤ (diskEquilibriumWeightConstant / (2 * (2 / Real.pi))) / a := by
  have hm : 0 < m := by linarith
  have hR : m ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  have hh := equilibriumDiscreteError_translated_radius_upper b a (Real.exp 1 * m + H)
    (2 / Real.pi) ha (hma.trans hR) (by positivity)
  change equilibriumDiscreteError _ _ _ ≤ _
  convert hh using 1 <;> ring

/-- All four estimates of (5.9), with explicit quantitative large-scale hypotheses. -/
theorem source_scale_estimates (b : Site) (m t A q H : ℝ) (hm : 2 ≤ m) (ht : 2 ≤ t)
    (hA : 4 ≤ A) (hq : 1 < q) (hcut : A ≤ m / t ^ 6)
    (hH : 0 ≤ H) (hHm : 5 * H ≤ m) (hd : 1 + sourceLowerTimeError ≤ Real.log m) :
    let I := geometricTerminalIndex A q (m / t ^ 6) (by linarith) hq hcut
    (∀ i ≤ I,
      |sourceEquilibriumTime b m (A * q ^ i) H - (sourceLowerTime m - Real.log (A * q ^ i))| ≤
        sourceEquilibriumTimeError + sourceLowerTimeError ∧
      sourceDiscreteError b m (A * q ^ i) H ≤
        (diskEquilibriumWeightConstant / (2 * (2 / Real.pi))) / (A * q ^ i)) ∧
    |sourceEquilibriumTime b m (A * q ^ I) H - 6 * Real.log t| ≤
      sourceEquilibriumTimeError + Real.log q ∧
    (I : ℝ) ≤ ((1 + sourceLowerTimeError) / Real.log q) * sourceLowerTime m := by
  have hA0 : 0 < A := by linarith
  let I := geometricTerminalIndex A q (m / t ^ 6) hA0 hq hcut
  have hd1 : 1 ≤ sourceLowerTime m := by
    have hh := (abs_le.mp (sourceLowerTime_log_bound m hm)).1
    linarith
  refine ⟨?_, source_terminal_energy_bound b m t A q H (by linarith) ht
    (by linarith) hq hcut hH hHm,
    source_terminal_index_linear_bound m t A q hm ht (by linarith) hq hcut hd1⟩
  intro i hi
  have ha := geometric_radius_ge A q hA0.le hq.le i
  have hma := source_terminal_radius_separation m t A q ht hA0 hq hcut i hi
  exact ⟨sourceEquilibriumTime_lowerTime_bound b m (A * q ^ i) H (by linarith) hma hH hHm,
    sourceDiscreteError_radius_upper b m (A * q ^ i) H (by linarith) hma hH⟩

end SRWTightness
