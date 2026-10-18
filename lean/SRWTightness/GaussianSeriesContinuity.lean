import SRWTightness.GaussianCoefficientGrowth
import SRWTightness.SchauderLevel
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

theorem gaussianSeries_majorant_summable (q : ℝ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (3 * ((n : ℝ) + 1)) * q ^ n / 2) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have h0 := summable_geometric_of_norm_lt_one hq
  have hs := (h1.add h0).mul_left (3 / 2 : ℝ)
  apply hs.congr
  intro n
  simp only [pow_one]
  ring

/-- The actual Gaussian series has continuous paths almost surely for any geometric amplitude. -/
theorem gaussianSeries_ae_continuous (q : ℝ) (hq0 : 0 ≤ q) (hq : ‖q‖ < 1) :
    ∀ᵐ ω ∂gaussianCoefficientLaw,
      Continuous (fun t ↦ ∑' n : ℕ,
        schauderLevel (2 ^ n) ((2 : ℝ) ^ n) (q ^ n) (fun k ↦ ω (some (n, k))) t) := by
  filter_upwards [gaussianCoefficient_dyadic_growth] with ω hω
  have hbound : ∀ᶠ n in atTop, ∀ t : ℝ,
      ‖schauderLevel (2 ^ n) ((2 : ℝ) ^ n) (q ^ n)
        (fun k ↦ ω (some (n, k))) t‖ ≤ (3 * ((n : ℝ) + 1)) * q ^ n / 2 := by
    filter_upwards [hω] with n hn
    intro t
    have hs : Real.sqrt (6 * (n : ℝ)) ≤ 3 * ((n : ℝ) + 1) := by
      have hsq := Real.sq_sqrt (show 0 ≤ 6 * (n : ℝ) by positivity)
      have hpos := Real.sqrt_nonneg (6 * (n : ℝ))
      nlinarith [sq_nonneg (n : ℝ)]
    simpa only [Real.norm_eq_abs] using schauderLevel_bound (2 ^ n) ((2 : ℝ) ^ n)
      (q ^ n) (3 * ((n : ℝ) + 1)) t (fun k ↦ ω (some (n, k)))
      (pow_nonneg hq0 n) (by positivity) (fun k hk ↦ (hn k hk).le.trans hs)
  have hu := tendstoUniformly_tsum_of_cofinite_eventually
    (f := fun n t ↦ schauderLevel (2 ^ n) ((2 : ℝ) ^ n) (q ^ n)
      (fun k ↦ ω (some (n, k))) t)
    (gaussianSeries_majorant_summable q hq) (by simpa [Nat.cofinite_eq_atTop] using hbound)
  apply hu.continuous
  apply Frequently.of_forall
  intro s
  exact continuous_finsetSum s (fun n _ ↦ schauderLevel_continuous _ _ _ _)

/-- The Gaussian series with the Brownian dyadic normalization. -/
noncomputable def gaussianDyadicPath (ω : GaussianCoefficientSpace) (t : ℝ) : ℝ :=
  t * ω none + ∑' n : ℕ, schauderLevel (2 ^ n) ((2 : ℝ) ^ n)
    ((Real.sqrt 2)⁻¹ ^ n) (fun k ↦ ω (some (n, k))) t

theorem gaussianDyadicPath_ae_continuous :
    ∀ᵐ ω ∂gaussianCoefficientLaw, Continuous (gaussianDyadicPath ω) := by
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : 1 < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hnorm : ‖(Real.sqrt 2)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_lt_one₀ hpos).mpr hlt
  filter_upwards [gaussianSeries_ae_continuous (Real.sqrt 2)⁻¹
    (inv_nonneg.mpr hpos.le) hnorm] with ω hω
  exact (continuous_id.mul continuous_const).add hω

end SRWTightness
