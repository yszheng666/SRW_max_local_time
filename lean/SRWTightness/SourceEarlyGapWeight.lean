import SRWTightness.SourceEarlyDistanceLevels

namespace SRWTightness

/-- The actual early logarithmic gap absorbs the cubic distance weight uniformly. -/
theorem source_early_gap_weight (a J₀ : ℕ)
    (hJ : sourceEarlyDistanceGap a J₀ ≤ a) :
    ((a : ℝ) + 1) ^ 2 * ((sourceEarlyDistanceGap a J₀ : ℝ) + 1) *
      Real.exp (-(sourceEarlyDistanceGap a J₀ : ℝ)) ≤ 1 := by
  let J := sourceEarlyDistanceGap a J₀
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log ((a : ℝ) + 1) ≤ Real.log ((a : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.log ((a : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hceil := Nat.le_ceil (20 * Real.log ((a : ℝ) + 2))
  have hlower : 20 * Real.log ((a : ℝ) + 2) ≤ (J : ℝ) := by
    dsimp [J, sourceEarlyDistanceGap]
    rw [Nat.cast_add]
    linarith [show (0 : ℝ) ≤ (J₀ : ℝ) from Nat.cast_nonneg _]
  have he : ((a : ℝ) + 1) ^ 3 ≤ Real.exp (J : ℝ) := by
    calc
      _ = Real.exp (3 * Real.log ((a : ℝ) + 1)) := by
        simpa only [Nat.cast_ofNat, Real.exp_log (by positivity : 0 < (a : ℝ) + 1)]
          using (Real.exp_nat_mul (Real.log ((a : ℝ) + 1)) 3).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hJr : (J : ℝ) ≤ a := Nat.cast_le.mpr hJ
  have hpoly : ((a : ℝ) + 1) ^ 2 * ((J : ℝ) + 1) ≤ Real.exp (J : ℝ) := by
    calc
      _ ≤ ((a : ℝ) + 1) ^ 2 * ((a : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ = ((a : ℝ) + 1) ^ 3 := by ring
      _ ≤ _ := he
  have hm := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-(J : ℝ))).le
  have hid : Real.exp (J : ℝ) * Real.exp (-(J : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero]
  exact hm.trans_eq hid

end SRWTightness
