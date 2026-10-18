import SRWTightness.ExternalBDZSquareMaximum
import SRWTightness.SourceUpperFineMaximumTail
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

theorem dyadic_log_scale_ge_one (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ Real.log ((2 : ℝ) ^ n) := by
  rw [Real.log_pow]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

/-- The dyadic BDZ input controls the actual positive fine maximum on each observed subset. -/
theorem bdz_dyadic_fine_maximum_tail (hBDZ : BDZDyadicSquareMaximumInput) :
    ∃ P c : ℝ, 0 < P ∧ 0 < c ∧ ∀ (a : Site) (n : ℕ), 2 ≤ n →
      ∀ (J : Finset (latticeSquareInterior a (2 ^ n))) (hJ : J.Nonempty) (u : ℝ),
      0 ≤ u →
      (finiteGaussianPositiveMaximumLaw (greenMatrix (latticeSquareInterior a (2 ^ n)))
        J hJ (Real.sqrt (2 / Real.pi))
        (2 * Real.log ((2 : ℝ) ^ n) - (3 / 4 : ℝ) *
          Real.log (Real.log ((2 : ℝ) ^ n)))).real (Ici u) ≤
        P * (1 + u) * Real.exp (-2 * u - c * u ^ 2 / Real.log ((2 : ℝ) ^ n)) := by
  obtain ⟨P, c, hP, hc, hBound⟩ := hBDZ
  refine ⟨P + Real.exp (2 + c), c, by positivity, hc, ?_⟩
  intro a n hn J hJ u hu
  apply source_upper_fine_positive_maximum_tail _ J hJ _ _ P c _ hP.le hc.le
    (dyadic_log_scale_ge_one n hn) _ u hu
  intro z hz
  refine LE.le.trans ?_ (hBound a n hn z hz)
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro φ ⟨x, hx, h⟩
  exact ⟨x, h⟩

end SRWTightness
