import SRWTightness.BoundedInjectiveMomentUniqueness

open MeasureTheory BoundedContinuousFunction
namespace SRWTightness

/-- Integer quadratic Laplace values determine a finite measure on the nonnegative half-line. -/
theorem nonnegative_quadratic_laplace_uniqueness (μ ν : Measure NNReal)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, (∫ x : NNReal, Real.exp (-(n : ℝ) * (x : ℝ) ^ 2) ∂μ) =
      ∫ x : NNReal, Real.exp (-(n : ℝ) * (x : ℝ) ^ 2) ∂ν) : μ = ν := by
  let f : NNReal →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ Real.exp (-(x : ℝ) ^ 2), by fun_prop⟩
    2 (by
      intro x y
      rw [Real.dist_eq]
      change |Real.exp (-(x : ℝ) ^ 2) - Real.exp (-(y : ℝ) ^ 2)| ≤ 2
      rw [abs_le]
      have hx := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (x : ℝ)))
      have hy := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (y : ℝ)))
      constructor <;> linarith [Real.exp_pos (-(x : ℝ) ^ 2), Real.exp_pos (-(y : ℝ) ^ 2)])
  apply bounded_injective_moment_uniqueness μ ν f
  · intro x y hxy
    apply NNReal.coe_injective
    have hh : Real.exp (-(x : ℝ) ^ 2) = Real.exp (-(y : ℝ) ^ 2) := hxy
    have he := Real.exp_injective hh
    nlinarith [x.property, y.property]
  · intro n
    have he (x : NNReal) : f x ^ n = Real.exp (-(n : ℝ) * (x : ℝ) ^ 2) := by
      change Real.exp (-(x : ℝ) ^ 2) ^ n = _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp_rw [he]
    exact h n

end SRWTightness
