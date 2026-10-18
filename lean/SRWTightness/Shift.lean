import SRWTightness.Law

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The future direction sequence after a deterministic number of steps. -/
def shift (n : ℕ) (ω : Sample) : Sample := fun k ↦ ω (n + k)

 theorem measurable_shift (n : ℕ) : Measurable (shift n) :=
  measurable_pi_lambda _ (fun k ↦ measurable_pi_apply (n + k))

 theorem shift_law (n : ℕ) : pathLaw.map (shift n) = pathLaw := by
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ directionLaw) (f := fun k ↦ n + k) (by
      intro i j h
      exact Nat.add_left_cancel h)

 theorem position_add (ω : Sample) (n k : ℕ) :
    position ω (n + k) = position ω n + position (shift n ω) k := by
  induction k with
  | zero => simp [position]
  | succ k ih =>
    change position ω (n + k) + step (ω (n + k)) =
      position ω n + (position (shift n ω) k + step (ω (n + k)))
    rw [ih, add_assoc]

 theorem localTime_add (ω : Sample) (n k : ℕ) (x : Site) :
    localTime ω (n + k) x = localTime ω n x +
      localTime (shift n ω) k (x - position ω n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, localTime_succ, ih, localTime_succ, position_add]
    have he : position ω n + position (shift n ω) k = x ↔
        position (shift n ω) k = x - position ω n := by
      constructor
      · intro h
        rw [← h]
        simp
      · intro h
        rw [h]
        simp
    simp only [he]
    omega

/-- Each translated half-open segment contributes no more visits than the full path. -/
theorem shifted_max_le (ω : Sample) (n k : ℕ) :
    maxLocalTime (shift n ω) k ≤ maxLocalTime ω (n + k) := by
  apply Finset.sup_le
  intro x hx
  have h := localTime_add ω n k (x + position ω n)
  have hb := localTime_le_max ω (n + k) (x + position ω n)
  simp only [add_sub_cancel_right] at h
  omega

end SRWTightness
