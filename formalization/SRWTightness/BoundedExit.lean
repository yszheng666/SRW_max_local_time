import SRWTightness.Filtration
import SRWTightness.Overshoot

open MeasureTheory

namespace SRWTightness

/-- The actual first exit clipped at a deterministic horizon. -/
noncomputable def boundedExit (R : ℝ) (N : ℕ) (ω : Sample) : WithTop ℕ :=
  min (exitTime R ω) N

 theorem boundedExit_ne_top (R : ℝ) (N : ℕ) (ω : Sample) : boundedExit R N ω ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (min_le_right _ _)

noncomputable def boundedTime (R : ℝ) (N : ℕ) (ω : Sample) : ℕ :=
  (boundedExit R N ω).untopA

 theorem coe_boundedTime (R : ℝ) (N : ℕ) (ω : Sample) :
    (boundedTime R N ω : WithTop ℕ) = boundedExit R N ω := by
  unfold boundedTime
  rw [WithTop.untopA_eq_untop (boundedExit_ne_top R N ω)]
  exact WithTop.coe_untop _ _

 theorem boundedTime_le (R : ℝ) (N : ℕ) (ω : Sample) : boundedTime R N ω ≤ N := by
  have h : (boundedTime R N ω : WithTop ℕ) ≤ N := by
    rw [coe_boundedTime]
    exact min_le_right _ _
  exact_mod_cast h

 theorem boundedExit_isStoppingTime (R : ℝ) (N : ℕ) : IsStoppingTime history (boundedExit R N) :=
  (exitTime_isStoppingTime R).min (isStoppingTime_const history N)

 theorem normSq_at_boundedTime_le {R : ℝ} (hR : 0 ≤ R) (N : ℕ) (ω : Sample) :
    normSq (position ω (boundedTime R N ω)) ≤ (R + 1) ^ 2 := by
  cases hk : boundedTime R N ω with
  | zero => simp [position, normSq, sq_nonneg]
  | succ k =>
    have hbefore : (k : WithTop ℕ) < exitTime R ω := by
      have hle : ((k + 1 : ℕ) : WithTop ℕ) ≤ exitTime R ω := by
        rw [← hk, coe_boundedTime]
        exact min_le_left _ _
      exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hle
    have hin := before_exit_mem R ω k hbefore
    change normSq (position ω k) < R ^ 2 at hin
    exact normSq_step_le (position ω k) (ω k) hR hin.le

 theorem normSq_at_boundedTime_ge_on_exit (R : ℝ) (N : ℕ) (ω : Sample)
    (h : exitTime R ω ≤ N) : R ^ 2 ≤ normSq (position ω (boundedTime R N ω)) := by
  apply normSq_at_exit_ge
  rw [coe_boundedTime]
  exact (min_eq_left h).symm

end SRWTightness
