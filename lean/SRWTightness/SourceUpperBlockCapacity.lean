import SRWTightness.SourceUpperComparisonScales
import SRWTightness.SourceUpperBlockObservation
import SRWTightness.SourceTerminalCapacityHalf

open Filter

namespace SRWTightness

/-- The exact floored fine radius has the required logarithmic separation from the terminal disk. -/
theorem source_upper_observation_log_gap (t : ℝ) :
    3 * sourceUpperLogRadius t / 4 - Real.log 2 ≤
      Real.log (sourceUpperRadius t) -
        Real.log (2 * upperTerminalFineRadius (sourceUpperLogRadius t)) := by
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  have hr : 0 < r := by
    change (0 : ℝ) < (sourceUpperBlockSide t : ℝ)
    exact_mod_cast sourceUpperBlockSide_pos t
  have hf : r ≤ Real.exp (sourceUpperLogRadius t / 4) := Nat.floor_le (Real.exp_pos _).le
  have hl := Real.log_le_log hr hf
  rw [Real.log_exp] at hl
  change _ ≤ Real.log (Real.exp (sourceUpperLogRadius t)) - Real.log (2 * r)
  rw [Real.log_exp, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr.ne']
  linarith only [hl]

/-- The actual upper block reference mark has at least one half of its mass at zero. -/
theorem source_upper_block_capacity_half :
    ∀ᶠ t : ℝ in atTop, ∀ b : Site,
      sourceUpperIntensity t * capacity
        (translateFinset b (diskFinset (Real.exp 1 * sourceUpperRadius t + sourceUpperBuffer t)))
        (sourceUpperBlock t b) ≤ 1 / 2 := by
  let C := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4
  filter_upwards [source_upper_record_scale_conditions 0 0 0 (by norm_num),
    sourceUpperLogRadius_eventually ((4 / 3) * (C + Real.log 2))] with t hs ht
  intro b
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  have hr : 1 ≤ r := by
    change (1 : ℝ) ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  have hH := hs.1
  have hHm := hs.2.1
  have hsep := hs.2.2.2.2.2
  have hgap := source_upper_observation_log_gap t
  exact source_terminal_capacity_half b (sourceUpperRadius t) (sourceUpperBuffer t) (2 * r)
    (sourceUpperBlock t b) (by linarith) (by linarith) (by linarith) (by linarith)
    (sourceUpperBlock_subset_observation_ball t b) (by
      change C ≤ _
      linarith only [ht, hgap])

end SRWTightness
