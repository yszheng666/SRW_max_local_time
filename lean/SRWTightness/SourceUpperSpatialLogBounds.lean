import SRWTightness.SourceUpperOnePointExponent

namespace SRWTightness

/-- The spatial logarithm is bounded at every lattice point, including the origin. -/
theorem source_upper_spatial_log_global (t : ℝ) (x : Site) :
    Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1) ≤ t := by
  have hm : 0 < max (Real.sqrt (normSq x)) 1 :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hratio : Real.exp t / max (Real.sqrt (normSq x)) 1 ≤ Real.exp t :=
    div_le_self (Real.exp_nonneg _) (le_max_right _ _)
  have hh := Real.log_le_log (div_pos (Real.exp_pos _) hm) hratio
  simpa only [Real.log_exp] using hh

/-- Outside the smaller radius exp(t)/t², the spatial logarithm costs only twice log(t). -/
theorem source_upper_spatial_log_outer (t : ℝ) (x : Site) (ht : 0 < t)
    (hx : Real.exp t / t ^ 2 ≤ Real.sqrt (normSq x)) :
    Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1) ≤ 2 * Real.log t := by
  have hm : 0 < max (Real.sqrt (normSq x)) 1 :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hden : Real.exp t / t ^ 2 ≤ max (Real.sqrt (normSq x)) 1 :=
    hx.trans (le_max_left _ _)
  have hratio : Real.exp t / max (Real.sqrt (normSq x)) 1 ≤ t ^ 2 := by
    have hh := div_le_div_of_nonneg_left (Real.exp_nonneg t) (by positivity) hden
    have heq : Real.exp t / (Real.exp t / t ^ 2) = t ^ 2 := by field_simp
    exact hh.trans_eq heq
  have hh := Real.log_le_log (div_pos (Real.exp_pos _) hm) hratio
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

end SRWTightness
