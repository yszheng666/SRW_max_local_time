import SRWTightness.SourceCoarseTerminalError

namespace SRWTightness

/-- Algebraic remainder after extracting the main coarse exponent. -/
theorem coarse_exponent_remainder (t d T l : ℝ) (hT : T ≠ 0) :
    ((2 * t - l) / T) ^ 2 * (T - d) / 2 - (2 * t - 2 * d - 2 * l) =
      -2 * (T - t) + (l + 2 * (T - t)) ^ 2 / (2 * T) -
        (((2 * t - l) / T - 2) * ((2 * t - l) / T + 2) * d) / 2 := by
  field_simp
  <;> ring

/-- A bounded total-time perturbation gives a bounded main-exponent remainder. -/
theorem coarse_exponent_remainder_bound (t d T l E : ℝ)
    (ht : 0 < t) (hT : t / 2 ≤ T) (hE : 0 ≤ E) (he : |T - t| ≤ E)
    (hl : l ^ 2 ≤ t) (hEt : 4 * E ^ 2 ≤ t) (hd : 0 ≤ d)
    (hs : 0 ≤ (2 * t - l) / T ∧ (2 * t - l) / T ≤ 4)
    (hw : |(2 * t - l) / T - 2| * d ≤ 1) :
    |((2 * t - l) / T) ^ 2 * (T - d) / 2 - (2 * t - 2 * d - 2 * l)| ≤
      2 * E + 7 := by
  have hT0 : 0 < T := by linarith
  have he2 : (T - t) ^ 2 ≤ E ^ 2 := by
    obtain ⟨hel, heu⟩ := abs_le.mp he
    nlinarith
  have hnum : (l + 2 * (T - t)) ^ 2 ≤ 4 * t := by
    nlinarith [sq_nonneg (l - 2 * (T - t))]
  have hmid0 : 0 ≤ (l + 2 * (T - t)) ^ 2 / (2 * T) := by positivity
  have hmid : (l + 2 * (T - t)) ^ 2 / (2 * T) ≤ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * T)).mpr
    nlinarith
  have hlast :
      |(((2 * t - l) / T - 2) * ((2 * t - l) / T + 2) * d) / 2| ≤ 3 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hd,
      abs_of_pos (show (0 : ℝ) < 2 by norm_num),
      abs_of_nonneg (show 0 ≤ (2 * t - l) / T + 2 by linarith [hs.1])]
    have hh := mul_le_mul_of_nonneg_left hs.2
      (mul_nonneg (abs_nonneg ((2 * t - l) / T - 2)) hd)
    nlinarith
  rw [coarse_exponent_remainder t d T l hT0.ne']
  calc
    _ ≤ |-2 * (T - t) + (l + 2 * (T - t)) ^ 2 / (2 * T)| +
        |(((2 * t - l) / T - 2) * ((2 * t - l) / T + 2) * d) / 2| :=
      abs_sub _ _
    _ ≤ (|-2 * (T - t)| + |(l + 2 * (T - t)) ^ 2 / (2 * T)|) + 3 :=
      add_le_add (abs_add_le _ _) hlast
    _ ≤ 2 * E + 7 := by
      rw [abs_mul, abs_of_nonneg hmid0]
      norm_num
      linarith

end SRWTightness
