import SRWTightness.SourceBufferedHalf

namespace SRWTightness

/-- Geometric radius at a source record level, with subtraction performed in the real exponent. -/
noncomputable def sourceRecordRadius (m : ℝ) (ℓ j : ℕ) : ℝ :=
  m * Real.exp ((ℓ : ℝ) - (j : ℝ))

/-- The source buffer includes the observation radius and the fixed lattice allowance. -/
def sourceRecordBuffer (r : ℝ) : ℝ := 4 * r + 10

theorem sourceRecordRadius_successor (m : ℝ) (ℓ j : ℕ) :
    Real.exp 1 * sourceRecordRadius m ℓ (j + 1) = sourceRecordRadius m ℓ j := by
  unfold sourceRecordRadius
  rw [show (ℓ : ℝ) - (j : ℝ) = 1 + ((ℓ : ℝ) - ((j + 1 : ℕ) : ℝ)) by push_cast; ring,
    Real.exp_add]
  ring

theorem sourceRecordRadius_two_steps (m : ℝ) (ℓ j : ℕ) :
    Real.exp 2 * sourceRecordRadius m ℓ (j + 2) = sourceRecordRadius m ℓ j := by
  unfold sourceRecordRadius
  rw [show (ℓ : ℝ) - (j : ℝ) = 2 + ((ℓ : ℝ) - ((j + 2 : ℕ) : ℝ)) by push_cast; ring,
    Real.exp_add]
  ring

theorem sourceRecordRadius_ge_terminal (m : ℝ) (hm : 0 ≤ m) (ℓ j : ℕ) (hj : j ≤ ℓ) :
    m ≤ sourceRecordRadius m ℓ j := by
  have hj' : (j : ℝ) ≤ ℓ := by exact_mod_cast hj
  have he : 1 ≤ Real.exp ((ℓ : ℝ) - (j : ℝ)) := Real.one_le_exp_iff.mpr (by linarith)
  unfold sourceRecordRadius
  nlinarith [mul_nonneg hm (sub_nonneg.mpr he)]

end SRWTightness
