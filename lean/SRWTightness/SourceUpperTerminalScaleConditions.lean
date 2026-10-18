import SRWTightness.ExternalExponentialFloorScale
import SRWTightness.DiskTerminalScaleTransfer

namespace SRWTightness

/-- The manuscript terminal depth, using the actual killed SRW Green function. -/
noncomputable def upperTerminalDepth (u : ℝ) : ℝ :=
  diskGreen (upperTerminalRadius u) 0 0 / (2 / Real.pi)

/-- Elementary scale growth and the proved Green diagonal estimate discharge terminal conditions. -/
theorem source_upper_terminal_scale_conditions (hScale : ExponentialFloorScaleInput)
    (c d₀ : ℝ) (hc : 0 < c) (hd₀ : 0 < d₀) :
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      2 ≤ upperTerminalRadius u ∧ 1 ≤ c * upperTerminalFineRadius u ∧
      64 * (c * upperTerminalFineRadius u) ≤ upperTerminalRadius u ∧
      d₀ ≤ upperTerminalDepth u ∧
      upperTerminalDepth u / 8 ≤ Real.log (c * upperTerminalFineRadius u) ∧
      Real.log (c * upperTerminalFineRadius u) + Real.log 64 ≤ upperTerminalDepth u / 2 := by
  let B := diskGreenEnergyConstant / (2 / Real.pi)
  have hB : 0 ≤ B := div_nonneg diskGreenEnergyConstant_pos.le (by positivity)
  have h64 : 0 ≤ Real.log (64 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨v₀, hv₀, hs⟩ := hScale c hc
  refine ⟨max v₀ (16 * (d₀ + B + |Real.log c| + Real.log 64 + 10)),
    hv₀.trans_le (le_max_left _ _), ?_⟩
  intro u hu
  have hv : v₀ ≤ u := (le_max_left _ _).trans hu
  have hlarge : 16 * (d₀ + B + |Real.log c| + Real.log 64 + 10) ≤ u :=
    (le_max_right _ _).trans hu
  obtain ⟨hR, hr, hcr, hsep, hLR, hLr⟩ := hs u hv
  have hdepth := disk_normalized_reference_log_bound (upperTerminalRadius u) hR
  change |upperTerminalDepth u - Real.log (upperTerminalRadius u)| ≤ B at hdepth
  have hd := abs_le.mp hdepth
  have hLR' := abs_le.mp hLR
  have hLr' := abs_le.mp hLr
  have hcl : -|Real.log c| ≤ Real.log c := neg_abs_le _
  have hcu : Real.log c ≤ |Real.log c| := le_abs_self _
  have ha : 0 ≤ |Real.log c| := abs_nonneg _
  have hr0 : 0 < upperTerminalFineRadius u := by linarith
  have he : Real.log (c * upperTerminalFineRadius u) =
      Real.log c + Real.log (upperTerminalFineRadius u) := Real.log_mul hc.ne' hr0.ne'
  refine ⟨hR, hcr, hsep, ?_, ?_, ?_⟩
  · linarith
  · rw [he]
    linarith
  · rw [he]
    linarith

end SRWTightness
