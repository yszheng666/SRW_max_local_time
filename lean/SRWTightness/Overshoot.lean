import SRWTightness.Exit
import SRWTightness.StepBound

namespace SRWTightness

/-- A finite first exit lands outside the open disk. -/
theorem normSq_at_exit_ge (R : ℝ) (ω : Sample) (n : ℕ)
    (ht : exitTime R ω = (n : WithTop ℕ)) : R ^ 2 ≤ normSq (position ω n) := by
  obtain ⟨k, hk, hout⟩ := (exitTime_le_iff R ω n).mp (le_of_eq ht)
  have htk : exitTime R ω ≤ (k : WithTop ℕ) :=
    (exitTime_le_iff R ω k).mpr ⟨k, le_rfl, hout⟩
  rw [ht] at htk
  have hnk : n ≤ k := by exact_mod_cast htk
  have he : k = n := Nat.le_antisymm hk hnk
  simpa [he] using hout

/-- Pathwise overshoot bound at every finite exit, before proving almost-sure exit. -/
theorem normSq_at_exit_le {R : ℝ} (hR : 0 ≤ R) (ω : Sample) (n : ℕ)
    (ht : exitTime R ω = (n : WithTop ℕ)) :
    normSq (position ω n) ≤ (R + 1) ^ 2 := by
  cases n with
  | zero => simp [position, normSq, sq_nonneg]
  | succ n =>
    have hbefore : (n : WithTop ℕ) < exitTime R ω := by
      rw [ht]
      exact_mod_cast Nat.lt_succ_self n
    have hin := before_exit_mem R ω n hbefore
    change normSq (position ω n) < R ^ 2 at hin
    exact normSq_step_le (position ω n) (ω n) hR hin.le

end SRWTightness
