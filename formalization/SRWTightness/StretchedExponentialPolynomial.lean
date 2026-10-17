import SRWTightness.StretchedExponentialSumInput
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace SRWTightness

/-- Every positive real power is uniformly dominated by a stretched exponential. -/
theorem stretched_exponential_polynomial_bound (p c γ : ℝ)
    (hp : 0 < p) (hc : 0 < c) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℝ, 0 ≤ d →
      d ^ p * Real.exp (-c * d ^ γ) ≤ C := by
  have ht : Tendsto (fun d : ℝ ↦ d ^ p * Real.exp (-c * d ^ γ)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / γ) c hc).comp
      (tendsto_rpow_atTop hγ)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with d hd
    dsimp only [Function.comp_apply]
    rw [← Real.rpow_mul hd, show γ * (p / γ) = p by field_simp]
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_order.1 ht).2 1 zero_lt_one)
  let U := max T 1
  refine ⟨max 1 (U ^ p), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro d hd
  by_cases hdT : T ≤ d
  · exact (hT d hdT).le.trans (le_max_left _ _)
  · have hdU : d ≤ U := (le_of_not_ge hdT).trans (le_max_left _ _)
    have he : Real.exp (-c * d ^ γ) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.rpow_nonneg hd γ))
    calc
      _ ≤ d ^ p := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hd p)
      _ ≤ U ^ p := Real.rpow_le_rpow hd hdU hp.le
      _ ≤ _ := le_max_right _ _

/-- The original quadratic stretched-exponential bound is internal. -/
theorem quadratic_stretched_exponential_bound_input_internal :
    QuadraticStretchedExponentialBoundInput := by
  intro c γ hc hγ
  obtain ⟨C, hC, hh⟩ := stretched_exponential_polynomial_bound 2 c γ (by norm_num) hc hγ
  refine ⟨C, hC, ?_⟩
  intro d hd
  simpa only [Real.rpow_two] using hh d (by linarith)

end SRWTightness
