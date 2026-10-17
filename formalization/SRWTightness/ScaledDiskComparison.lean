import SRWTightness.DiskTimeComparison
import Mathlib.Tactic.FieldSimp

open MeasureTheory

namespace SRWTightness

 theorem scaled_radius_error_identity (A x : ℝ) (hA : A ≠ 0) (hx : x ≠ 0) :
    (x / A + 1) ^ 2 / x ^ 2 + x ^ 2 / (A * x) ^ 2 =
      2 / A ^ 2 + 2 / (A * x) + 1 / x ^ 2 := by
  field_simp
  <;> ring

/-- Source equation (11.2), with the exact finite-time error. -/
theorem prob_scaled_disk_comparison_failure (A : ℝ) (hA : 1 < A)
    (n : ℕ) (hn : 1 ≤ n) :
    pathLaw.real {ω | ¬ (exitTime (Real.sqrt n / A) ω ≤ n ∧
      (n : WithTop ℕ) ≤ exitTime (A * Real.sqrt n) ω)} ≤
      2 / A ^ 2 + 2 / (A * Real.sqrt n) + 1 / n := by
  have hAp : 0 < A := lt_trans zero_lt_one hA
  have hnp : 0 < n := hn
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hnp
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
  have hb := prob_disk_time_comparison_failure
    (div_nonneg hs.le hAp.le) (mul_pos hAp hs) n hnp
  have he := scaled_radius_error_identity A (Real.sqrt n) (ne_of_gt hAp) (ne_of_gt hs)
  rw [Real.sq_sqrt hnr.le] at he
  exact hb.trans_eq he

/-- Source equation (11.3), accounting explicitly for the null infinite-exit set. -/
theorem ae_scaled_disk_time_sandwich (A : ℝ) (hA : 1 < A) (n : ℕ) :
    ∀ᵐ ω ∂pathLaw, (exitTime (Real.sqrt n / A) ω ≤ n ∧
      (n : WithTop ℕ) ≤ exitTime (A * Real.sqrt n) ω) →
      diskMax (Real.sqrt n / A) ω ≤ maxLocalTime ω n ∧
      maxLocalTime ω n ≤ diskMax (A * Real.sqrt n) ω := by
  have hAp : 0 ≤ A := (lt_trans zero_lt_one hA).le
  filter_upwards [exitTime_ne_top_ae (div_nonneg (Real.sqrt_nonneg _) hAp),
    exitTime_ne_top_ae (mul_nonneg hAp (Real.sqrt_nonneg _))] with ω hi ho
  intro he
  exact disk_time_sandwich _ _ ω n he.1 he.2 hi ho

end SRWTightness
