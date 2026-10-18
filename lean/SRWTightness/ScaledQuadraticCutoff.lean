import SRWTightness.QuadraticCutoffDerivative

namespace SRWTightness

/-- The scalar profile at smoothing scale epsilon. -/
noncomputable def scaledQuadraticCutoff (ε x : ℝ) : ℝ := quadraticCutoff (x / ε)

theorem scaledQuadraticCutoff_bounds (ε x : ℝ) :
    0 ≤ scaledQuadraticCutoff ε x ∧ scaledQuadraticCutoff ε x ≤ 1 :=
  quadraticCutoff_bounds (x / ε)

theorem scaledQuadraticCutoff_eq_one (ε x : ℝ) (hε : 0 < ε) (hx : x ≤ 0) :
    scaledQuadraticCutoff ε x = 1 :=
  quadraticCutoff_eq_one _ (div_nonpos_of_nonpos_of_nonneg hx hε.le)

theorem scaledQuadraticCutoff_eq_zero (ε x : ℝ) (hε : 0 < ε) (hx : ε ≤ x) :
    scaledQuadraticCutoff ε x = 0 := by
  apply quadraticCutoff_eq_zero
  exact (le_div_iff₀ hε).mpr (by simpa using hx)

/-- The derivative under rescaling is exact, including the scaled junctions. -/
theorem scaledQuadraticCutoff_hasDerivAt (ε x : ℝ) :
    HasDerivAt (scaledQuadraticCutoff ε) (quadraticCutoffSlope (x / ε) / ε) x := by
  apply ((quadraticCutoff_hasDerivAt (x / ε)).comp x
    ((hasDerivAt_id x).div_const ε)).congr_deriv
  simp [div_eq_mul_inv]

theorem scaledQuadraticCutoff_deriv (ε x : ℝ) :
    deriv (scaledQuadraticCutoff ε) x = quadraticCutoffSlope (x / ε) / ε :=
  (scaledQuadraticCutoff_hasDerivAt ε x).deriv

/-- The derivative is bounded by two over the smoothing scale. -/
theorem scaledQuadraticCutoff_deriv_bound (ε x : ℝ) (hε : 0 < ε) :
    |deriv (scaledQuadraticCutoff ε) x| ≤ 2 / ε := by
  rw [scaledQuadraticCutoff_deriv, abs_div, abs_of_pos hε]
  apply div_le_div_of_nonneg_right _ hε.le
  have hh := quadraticCutoffSlope_bounds (x / ε)
  exact abs_le.mpr ⟨hh.1, hh.2.trans (by norm_num)⟩

/-- The derivative variation has the required inverse-square scaling. -/
theorem scaledQuadraticCutoff_deriv_dist (ε x y : ℝ) (hε : 0 < ε) :
    |deriv (scaledQuadraticCutoff ε) x - deriv (scaledQuadraticCutoff ε) y| ≤
      (4 / ε ^ 2) * |x - y| := by
  simp only [scaledQuadraticCutoff_deriv, ← sub_div, abs_div, abs_of_pos hε]
  have hh := div_le_div_of_nonneg_right (quadraticCutoffSlope_dist (x / ε) (y / ε)) hε.le
  rw [← sub_div, abs_div, abs_of_pos hε] at hh
  exact hh.trans_eq (by field_simp)

end SRWTightness
