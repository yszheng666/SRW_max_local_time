import SRWTightness.BoundedInjectiveMomentUniqueness

open MeasureTheory BoundedContinuousFunction
namespace SRWTightness

/-- Nonnegative integer Laplace values determine a finite measure on the nonnegative half-line. -/
theorem nonnegative_laplace_uniqueness (μ ν : Measure NNReal)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, (∫ x : NNReal, Real.exp (-(n : ℝ) * x) ∂μ) =
      ∫ x : NNReal, Real.exp (-(n : ℝ) * x) ∂ν) : μ = ν := by
  let f : NNReal →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ Real.exp (-(x : ℝ)), Real.continuous_exp.comp NNReal.continuous_coe.neg⟩
    2 (by
      intro x y
      rw [Real.dist_eq]
      change |Real.exp (-(x : ℝ)) - Real.exp (-(y : ℝ))| ≤ 2
      have hx := Real.exp_le_one_iff.mpr (neg_nonpos.mpr x.property)
      have hy := Real.exp_le_one_iff.mpr (neg_nonpos.mpr y.property)
      calc
        _ ≤ |Real.exp (-(x : ℝ))| + |Real.exp (-(y : ℝ))| := abs_sub _ _
        _ ≤ 2 := by
          rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
          exact (add_le_add hx hy).trans_eq (by norm_num))
  apply bounded_injective_moment_uniqueness μ ν f
  · intro x y hxy
    apply NNReal.coe_injective
    have hh : Real.exp (-(x : ℝ)) = Real.exp (-(y : ℝ)) := hxy
    exact neg_injective (Real.exp_injective hh)
  · intro n
    have he (x : NNReal) : f x ^ n = Real.exp (-(n : ℝ) * x) := by
      change Real.exp (-(x : ℝ)) ^ n = _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp_rw [he]
    exact h n

end SRWTightness
