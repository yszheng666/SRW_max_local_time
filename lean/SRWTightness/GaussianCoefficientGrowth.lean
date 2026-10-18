import SRWTightness.GaussianCoefficientTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace SRWTightness

/-- Summable layer tail bounds imply an eventual bound on every coefficient in each layer. -/
theorem gaussianCoefficient_eventually_bounded (N : ℕ → ℕ) (r : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ r n)
    (hs : Summable (fun n ↦ (N n : ℝ) * (2 * Real.exp (-(r n) ^ 2 / 2)))) :
    ∀ᵐ ω ∂gaussianCoefficientLaw, ∀ᶠ n in atTop,
      ∀ k < N n, |ω (some (n, k))| < r n := by
  let E : ℕ → Set GaussianCoefficientSpace :=
    fun n ↦ {ω | ∃ k < N n, r n ≤ |ω (some (n, k))|}
  have hm : ∀ n, gaussianCoefficientLaw (E n) ≤
      ENNReal.ofReal ((N n : ℝ) * (2 * Real.exp (-(r n) ^ 2 / 2))) := by
    intro n
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (gaussianCoefficient_layer_tail n (N n) (r n) (hr n))
  have ht : (∑' n, gaussianCoefficientLaw (E n)) ≠ ∞ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hm)
  filter_upwards [ae_eventually_notMem ht] with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  exact lt_of_not_ge (fun h ↦ hn ⟨k, hk, h⟩)

theorem gaussianCoefficient_dyadic_tail_summable :
    Summable (fun n : ℕ ↦ ((2 ^ n : ℕ) : ℝ) *
      (2 * Real.exp (-(Real.sqrt (6 * (n : ℝ))) ^ 2 / 2))) := by
  have hlog : Real.log 2 - 3 < 0 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hs := (Real.summable_exp_nat_mul_iff.mpr hlog).mul_left 2
  apply hs.congr
  intro n
  symm
  rw [Real.sq_sqrt (by positivity)]
  have hp : ((2 ^ n : ℕ) : ℝ) = Real.exp ((n : ℝ) * Real.log 2) := by
    simp [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hp]
  rw [show (n : ℝ) * (Real.log 2 - 3) =
    (n : ℝ) * Real.log 2 + -(6 * (n : ℝ)) / 2 by ring, Real.exp_add]
  ring

theorem gaussianCoefficient_dyadic_growth :
    ∀ᵐ ω ∂gaussianCoefficientLaw, ∀ᶠ (n : ℕ) in atTop,
      ∀ k < 2 ^ n, |ω (some (n, k))| < Real.sqrt (6 * (n : ℝ)) :=
  gaussianCoefficient_eventually_bounded (fun n ↦ 2 ^ n)
    (fun n ↦ Real.sqrt (6 * (n : ℝ))) (fun _ ↦ Real.sqrt_nonneg _)
    gaussianCoefficient_dyadic_tail_summable

end SRWTightness
