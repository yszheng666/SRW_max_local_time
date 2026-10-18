import SRWTightness.ExitTail
import SRWTightness.ExitProbability

open MeasureTheory

namespace SRWTightness

 theorem disk_time_sandwich (r R : ℝ) (ω : Sample) (n : ℕ)
    (hr : exitTime r ω ≤ n) (hR : (n : WithTop ℕ) ≤ exitTime R ω)
    (hfinr : exitTime r ω ≠ ⊤) (hfinR : exitTime R ω ≠ ⊤) :
    diskMax r ω ≤ maxLocalTime ω n ∧ maxLocalTime ω n ≤ diskMax R ω := by
  rw [← coe_exitSteps r ω hfinr] at hr
  rw [← coe_exitSteps R ω hfinR] at hR
  exact max_time_sandwich ω n (exitSteps r ω) (exitSteps R ω)
    (WithTop.coe_le_coe.mp hr) (WithTop.coe_le_coe.mp hR)

/-- The failure probability of placing a fixed time between two disk exits. -/
theorem prob_disk_time_comparison_failure {r R : ℝ} (hr : 0 ≤ r) (hR : 0 < R)
    (n : ℕ) (hn : 0 < n) :
    pathLaw.real {ω | ¬ (exitTime r ω ≤ n ∧ (n : WithTop ℕ) ≤ exitTime R ω)} ≤
      (r + 1) ^ 2 / n + (n : ℝ) / R ^ 2 := by
  have hsub : {ω | ¬ (exitTime r ω ≤ n ∧ (n : WithTop ℕ) ≤ exitTime R ω)} ⊆
      {ω | (n : WithTop ℕ) < exitTime r ω} ∪ {ω | exitTime R ω ≤ n} := by
    intro ω hω
    by_cases h : exitTime r ω ≤ n
    · exact Or.inr (le_of_lt (lt_of_not_ge (fun h' ↦ hω ⟨h, h'⟩)))
    · exact Or.inl (lt_of_not_ge h)
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (prob_exit_gt hr n hn) (prob_exit_le R hR n)))

end SRWTightness
