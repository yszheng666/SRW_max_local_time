import SRWTightness.SourceLowerRadius
import SRWTightness.SourceLowerTime

namespace SRWTightness

noncomputable def sourceScaleThreshold (A : ℝ) : ℝ :=
  max A (Real.exp (max 10 (1 + sourceLowerTimeError)))

/-- One explicit threshold supplies every elementary large-scale condition for H_0=14. -/
theorem sourceScaleThreshold_conditions (t A : ℝ) (hA : 4 ≤ A)
    (ht : sourceScaleThreshold A ≤ t) :
    2 ≤ t ∧ A ≤ sourceLowerRadius t / t ^ 6 ∧ 70 ≤ sourceLowerRadius t ∧
      1 + sourceLowerTimeError ≤ Real.log (sourceLowerRadius t) := by
  have hA0 : 0 < A := by linarith
  have hAt : A ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := hA0.trans_le hAt
  have htexp : Real.exp (max 10 (1 + sourceLowerTimeError)) ≤ t :=
    (le_max_right _ _).trans ht
  have hlog := Real.log_le_log (Real.exp_pos _) htexp
  rw [Real.log_exp] at hlog
  have hlog10 : 10 ≤ Real.log t := (le_max_left _ _).trans hlog
  have hlogE : 1 + sourceLowerTimeError ≤ Real.log t := (le_max_right _ _).trans hlog
  have hD := sourceLowerLogRadius_ge_seven_log t (by linarith)
  have hcut := sourceLowerRadius_cutoff_nonempty t A ht0 hA0 (by linarith)
    (Real.log_le_log hA0 hAt)
  have hm := Real.add_one_le_exp (sourceLowerLogRadius t)
  have hm70 : 70 ≤ sourceLowerRadius t := by unfold sourceLowerRadius; linarith
  refine ⟨by linarith, hcut, hm70, ?_⟩
  rw [log_sourceLowerRadius]
  linarith

end SRWTightness
