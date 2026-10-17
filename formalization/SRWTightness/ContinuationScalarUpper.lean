import SRWTightness.SourceContinuationUpper

namespace SRWTightness

/-- Normalize the continuation prefactor while retaining the actual initial height. -/
theorem continuation_scalar_upper (t L x u q ν θ : ℝ)
    (ht : 0 < t) (hL : t / 2 ≤ L) (hu : t ≤ u) (hq : 0 ≤ q)
    (hν : 0 ≤ ν) (hθ : θ ≤ 4) (hx : 0 ≤ x) (hxA : x ≤ 4 + θ * ν) :
    ((5 + θ * ν - x) * (5 + q) / L) *
        Real.exp (-((x - u) ^ 2 / (2 * L))) * Real.sqrt (x / (u * L)) ≤
      100 * (ν + 1) * (1 + q) * Real.sqrt x / t ^ 2 *
        Real.exp (-((x - u) ^ 2 / (2 * L))) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := ht.trans_le hu
  have hmargin : 0 ≤ 5 + θ * ν - x := by linarith
  have hθν := mul_le_mul_of_nonneg_right hθ hν
  have ha : (5 + θ * ν - x) * (5 + q) ≤ 25 * (ν + 1) * (1 + q) := by
    have h1 : 5 + θ * ν - x ≤ 5 * (ν + 1) := by linarith
    have h2 : 5 + q ≤ 5 * (1 + q) := by linarith
    have hh := mul_le_mul h1 h2 (by linarith : 0 ≤ 5 + q)
      (by positivity : 0 ≤ 5 * (ν + 1))
    nlinarith
  have hcoef : (5 + θ * ν - x) * (5 + q) / L ≤
      50 * (ν + 1) * (1 + q) / t := by
    apply (div_le_div_iff₀ hL0 ht).mpr
    have h1 := mul_le_mul_of_nonneg_right ha ht.le
    have h2 := mul_nonneg (show 0 ≤ 2 * L - t by linarith)
      (show 0 ≤ 25 * (ν + 1) * (1 + q) by positivity)
    nlinarith
  have hden : t ^ 2 ≤ 4 * (u * L) := by
    have hh := mul_le_mul hu hL (by linarith : 0 ≤ t / 2) hu0.le
    nlinarith [sq_nonneg t]
  have hratio : x / (u * L) ≤ 4 * x / t ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < u * L) (by positivity : 0 < t ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden hx]
  have hroot : Real.sqrt (x / (u * L)) ≤ 2 * Real.sqrt x / t := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * Real.sqrt x / t)).mpr
    calc
      _ ≤ 4 * x / t ^ 2 := hratio
      _ = (2 * Real.sqrt x / t) ^ 2 := by rw [div_pow, mul_pow, Real.sq_sqrt hx]; ring
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)) hroot
    (Real.sqrt_nonneg _) (by positivity : 0 ≤
      (50 * (ν + 1) * (1 + q) / t) * Real.exp (-((x - u) ^ 2 / (2 * L))))
  calc
    _ ≤ (50 * (ν + 1) * (1 + q) / t * Real.exp (-((x - u) ^ 2 / (2 * L)))) *
        (2 * Real.sqrt x / t) := hh
    _ = _ := by ring

end SRWTightness
