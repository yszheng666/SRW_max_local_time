import SRWTightness.SourceRecordRadii

namespace SRWTightness

/-- A source radius ratio grows linearly in the difference of the source levels. -/
theorem source_level_log_ratio (m d : ℝ) (ℓ j ν : ℕ) (hm : 0 < m)
    (hbuffer : 14 ≤ sourceRecordRadius m ℓ j)
    (hd : sourceRecordRadius m ℓ ν / 2 ≤ d) :
    Real.log (2 * (sourceRecordRadius m ℓ j + 14) / d) ≤
      (ν : ℝ) - (j : ℝ) + 3 * Real.log 2 := by
  have hp (k : ℕ) : 0 < sourceRecordRadius m ℓ k := by
    unfold sourceRecordRadius
    positivity
  have hpν := hp ν
  have hpj := hp j
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hu := Real.log_le_log
    (by positivity : 0 < 2 * (sourceRecordRadius m ℓ j + 14))
    (show 2 * (sourceRecordRadius m ℓ j + 14) ≤
      4 * sourceRecordRadius m ℓ j by linarith)
  have hl := Real.log_le_log (by positivity : 0 < sourceRecordRadius m ℓ ν / 2) hd
  have hlog (k : ℕ) : Real.log (sourceRecordRadius m ℓ k) =
      Real.log m + (ℓ : ℝ) - (k : ℝ) := by
    simp [sourceRecordRadius, Real.log_mul hm.ne' (Real.exp_pos _).ne']
    ring
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (hp j).ne', hlog j] at hu
  rw [Real.log_div (hp ν).ne' (by norm_num : (2 : ℝ) ≠ 0), hlog ν] at hl
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_div (by positivity) hd0.ne']
  linarith

/-- The actual early indices convert the level difference to twice the gap plus five. -/
theorem source_early_gap_log_ratio (m d : ℝ) (ℓ a J : ℕ) (hm : 0 < m)
    (hJa : J ≤ a) (hbuffer : 14 ≤ sourceRecordRadius m ℓ (a - J))
    (hd : sourceRecordRadius m ℓ (a + J + 5) / 2 ≤ d) :
    Real.log (2 * (sourceRecordRadius m ℓ (a - J) + 14) / d) ≤
      2 * (J : ℝ) + 5 + 3 * Real.log 2 := by
  have hh := source_level_log_ratio m d ℓ (a - J) (a + J + 5) hm hbuffer hd
  rw [Nat.cast_sub hJa] at hh
  push_cast at hh
  linarith

end SRWTightness
