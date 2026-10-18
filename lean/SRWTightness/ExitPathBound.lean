import SRWTightness.ExitMoment

namespace SRWTightness

/-- Uniform overshoot bound for every point of a killed segment, including its endpoint. -/
theorem normSq_up_to_exitSteps {R : ℝ} (hR : 0 ≤ R) (ω : Sample)
    (hfin : exitTime R ω ≠ ⊤) (k : ℕ) (hk : k ≤ exitSteps R ω) :
    normSq (position ω k) ≤ (R + 1) ^ 2 := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · have he : (k : WithTop ℕ) < exitTime R ω := by
      rw [← coe_exitSteps R ω hfin]
      exact WithTop.coe_lt_coe.mpr hlt
    have hd := before_exit_mem R ω k he
    change normSq (position ω k) < R ^ 2 at hd
    nlinarith
  · rw [heq]
    exact normSq_at_exit_le hR ω _ (coe_exitSteps R ω hfin).symm

end SRWTightness
