import SRWTightness.BufferedRecordProbability

namespace SRWTightness

/-- Geometric source radius indexed outwards from the terminal observation scale. -/
noncomputable def growingRecordRadius (m : ℝ) (n : ℕ) : ℝ := m * Real.exp (n : ℝ)

noncomputable def growingRecordEntrance (b : Site) (m H : ℝ) (n : ℕ) : Finset Site :=
  translateFinset b (diskFinset (growingRecordRadius m n - H))

noncomputable def growingRecordExit (b : Site) (m H : ℝ) (n : ℕ) : Finset Site :=
  translateFinset b (diskFinset (Real.exp 1 * growingRecordRadius m n + H))

@[simp] theorem growingRecordRadius_zero (m : ℝ) : growingRecordRadius m 0 = m := by
  simp [growingRecordRadius]

theorem growingRecordRadius_succ (m : ℝ) (n : ℕ) :
    growingRecordRadius m (n + 1) = Real.exp 1 * growingRecordRadius m n := by
  simp only [growingRecordRadius, Nat.cast_add, Nat.cast_one, Real.exp_add]
  ring

theorem growingRecordRadius_ge_base (m : ℝ) (hm : 0 ≤ m) (n : ℕ) :
    m ≤ growingRecordRadius m n := by
  have he : 1 ≤ Real.exp (n : ℝ) := Real.one_le_exp_iff.mpr (by positivity)
  dsimp [growingRecordRadius]
  nlinarith

theorem growingRecordExit_succ (b : Site) (m H : ℝ) (n : ℕ) :
    growingRecordExit b m H (n + 1) =
      translateFinset b (diskFinset (Real.exp 2 * growingRecordRadius m n + H)) := by
  rw [growingRecordExit, growingRecordRadius_succ]
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [he, mul_assoc]

end SRWTightness
