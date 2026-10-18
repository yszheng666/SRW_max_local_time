import SRWTightness.ThirdCgfCenteredMoment

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace SRWTightness

/-- The cubic Taylor remainder of a cgf is controlled by its actual third derivative
throughout the segment, for either sign of the tilt parameter. -/
theorem cgf_taylor_third_remainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (t C : ℝ) (hC : 0 ≤ C)
    (hs : uIcc 0 t ⊆ interior (integrableExpSet X μ))
    (hb : ∀ s ∈ uIcc 0 t, |iteratedDeriv 3 (cgf X μ) s| ≤ C) :
    |cgf X μ t - (∫ ω, X ω ∂μ) * t -
      ((∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2) * t ^ 2 / 2| ≤ C * |t| ^ 3 / 6 := by
  by_cases ht : t = 0
  · simp [ht]
  have hu : UniqueDiffOn ℝ (uIcc 0 t) := uniqueDiffOn_uIcc (Ne.symm ht)
  have h0 := hs (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 t)
  have hpoly : taylorWithinEval (cgf X μ) 2 (uIcc 0 t) 0 t =
      (∫ ω, X ω ∂μ) * t +
        ((∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2) * t ^ 2 / 2 := by
    have hd (n : ℕ) : iteratedDerivWithin n (cgf X μ) (uIcc 0 t) 0 =
        iteratedDeriv n (cgf X μ) 0 :=
      iteratedDerivWithin_eq_iteratedDeriv hu (analyticAt_cgf h0).contDiffAt left_mem_uIcc
    simp only [show (2 : ℕ) = 1 + 1 from rfl, taylorWithinEval_succ,
      taylor_within_zero_eval, hd]
    rw [iteratedDeriv_one, deriv_cgf_zero h0, iteratedDeriv_two_cgf h0,
      deriv_cgf_zero h0]
    simp only [cgf_zero, zero_mul, Real.exp_zero, mul_one, mgf_zero, div_one]
    norm_num
    ring
  obtain ⟨s, hst, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := cgf X μ) (n := 2) (Ne.symm ht) ((analyticOn_cgf.mono hs).contDiffOn hu)
  rw [hpoly] at he
  have he' : cgf X μ t - (∫ ω, X ω ∂μ) * t -
      ((∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2) * t ^ 2 / 2 =
        iteratedDeriv 3 (cgf X μ) s * t ^ 3 / 6 := by
    simpa [Nat.factorial, sub_add_eq_sub_sub] using he
  rw [he', abs_div, abs_mul, abs_pow]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hb s ⟨hst.1.le, hst.2.le⟩) (by positivity)) (by norm_num)

end SRWTightness
