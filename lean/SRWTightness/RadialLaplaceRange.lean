import SRWTightness.RadialLaplaceSubstitution

namespace SRWTightness

/-- The squared radial Laplace substitution is a rational function. -/
theorem radial_laplace_substitution_sq (s t : ℝ) (hs : 0 ≤ s) :
    (t / Real.sqrt (1 + 2 * s * t ^ 2)) ^ 2 = t ^ 2 / (1 + 2 * s * t ^ 2) := by
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + 2 * s * t ^ 2)]

/-- The radial Laplace substitution maps the positive half-line onto its exact finite interval. -/
theorem radial_laplace_substitution_image (s : ℝ) (hs : 0 < s) :
    (fun t : ℝ ↦ t / Real.sqrt (1 + 2 * s * t ^ 2)) '' Set.Ioi 0 =
      Set.Ioo 0 (1 / Real.sqrt (2 * s)) := by
  have hS : 0 < Real.sqrt (2 * s) := Real.sqrt_pos.mpr (by positivity)
  have hSsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * s)
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hA : 0 < Real.sqrt (1 + 2 * s * t ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hAsq := Real.sq_sqrt (by positivity : 0 ≤ 1 + 2 * s * t ^ 2)
    refine ⟨div_pos ht hA, ?_⟩
    apply (div_lt_div_iff₀ hA hS).mpr
    have he : (t * Real.sqrt (2 * s)) ^ 2 = 2 * s * t ^ 2 := by
      rw [mul_pow, hSsq]
      ring
    nlinarith [mul_pos ht hS]
  · intro hu
    have huS : u * Real.sqrt (2 * s) < 1 := (lt_div_iff₀ hS).mp hu.2
    have hmul : 0 < u * Real.sqrt (2 * s) := mul_pos hu.1 hS
    have hsq : (u * Real.sqrt (2 * s)) ^ 2 = 2 * s * u ^ 2 := by
      rw [mul_pow, hSsq]
      ring
    have hden : 0 < 1 - 2 * s * u ^ 2 := by nlinarith
    let t := u / Real.sqrt (1 - 2 * s * u ^ 2)
    have ht : 0 < t := div_pos hu.1 (Real.sqrt_pos.mpr hden)
    refine ⟨t, ht, ?_⟩
    have he : (t / Real.sqrt (1 + 2 * s * t ^ 2)) ^ 2 = u ^ 2 := by
      rw [radial_laplace_substitution_sq s t hs.le]
      dsimp [t]
      rw [div_pow, Real.sq_sqrt hden.le]
      have hn : 1 - 2 * s * u ^ 2 ≠ 0 := ne_of_gt hden
      have hd : 1 + 2 * s * (u ^ 2 / (1 - 2 * s * u ^ 2)) ≠ 0 :=
        ne_of_gt (by positivity)
      apply (div_eq_iff hd).mpr
      have hcancel := div_mul_cancel₀ (u ^ 2) hn
      nlinarith [hcancel]
    have hpos : 0 < t / Real.sqrt (1 + 2 * s * t ^ 2) :=
      div_pos ht (Real.sqrt_pos.mpr (by positivity))
    change t / Real.sqrt (1 + 2 * s * t ^ 2) = u
    nlinarith [hu.1]

end SRWTightness
