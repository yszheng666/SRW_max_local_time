import SRWTightness.UpperRootGaussianIntegral

open MeasureTheory

namespace SRWTightness

/-- The geometrically weighted root contribution; its zero-root term is zero. -/
noncomputable def upperGeometricRootTerm (q a : ℝ) (J : ℕ) : ℝ :=
  (1 - 1 / q) ^ (J - 1) * (J : ℝ) ^ (1 / 4 : ℝ) *
    Real.exp (a * Real.sqrt (2 * (J : ℝ)))

/-- Uniform finite root-number sum bound, retaining the exact extracted exponential. -/
theorem upper_geometric_root_sum_finite :
    ∃ C : ℝ, 0 < C ∧ ∀ q a : ℝ, 1 ≤ q → 0 ≤ a → a ≤ 3 → ∀ M : ℕ,
      (∑ J ∈ Finset.range M, upperGeometricRootTerm q a J) ≤
        C * q ^ 2 * Real.exp (a ^ 2 * q / 2) := by
  obtain ⟨K, hK, hIntegral⟩ := upper_root_gaussian_integral_bound
  refine ⟨(Real.exp 1) ^ 2 * K, by positivity, ?_⟩
  intro q a hq ha hcap M
  have hq0 : 0 < q := by linarith
  have hI := hIntegral q (a * q) hq (mul_nonneg ha hq0.le)
    (mul_le_mul_of_nonneg_right hcap hq0.le) M
  have hkernel := (upper_root_gaussian_sum_integral q (a * q) M hq).trans
    (mul_le_mul_of_nonneg_left hI (Real.exp_nonneg 1))
  have hpoint (J : ℕ) : upperGeometricRootTerm q a J ≤
      Real.exp 1 * Real.exp (a ^ 2 * q / 2) * ((J : ℝ) ^ (1 / 4 : ℝ) *
        Real.exp (-((Real.sqrt (2 * (J : ℝ)) - a * q) ^ 2 / (2 * q)))) := by
    by_cases hJ : J = 0
    · simp only [upperGeometricRootTerm, hJ, Nat.cast_zero,
        Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero, zero_mul, le_refl]
    · exact upper_geometric_root_gaussian q a J hq (Nat.pos_of_ne_zero hJ)
  calc
    _ ≤ ∑ J ∈ Finset.range M, Real.exp 1 * Real.exp (a ^ 2 * q / 2) *
        ((J : ℝ) ^ (1 / 4 : ℝ) *
          Real.exp (-((Real.sqrt (2 * (J : ℝ)) - a * q) ^ 2 / (2 * q)))) :=
      Finset.sum_le_sum (fun J _ ↦ hpoint J)
    _ = (Real.exp 1 * Real.exp (a ^ 2 * q / 2)) *
        ∑ J ∈ Finset.range M, (J : ℝ) ^ (1 / 4 : ℝ) *
          Real.exp (-((Real.sqrt (2 * (J : ℝ)) - a * q) ^ 2 / (2 * q))) := by
      rw [Finset.mul_sum]
    _ ≤ (Real.exp 1 * Real.exp (a ^ 2 * q / 2)) * (Real.exp 1 * (K * q ^ 2)) :=
      mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = _ := by ring

/-- Source (4.27): the infinite geometric root sum is summable with the exact quadratic cost. -/
theorem upper_geometric_root_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q a : ℝ, 1 ≤ q → 1 / 2 ≤ a → a ≤ 3 →
      Summable (upperGeometricRootTerm q a) ∧
        (∑' J : ℕ, upperGeometricRootTerm q a J) ≤
          C * q ^ 2 * Real.exp (a ^ 2 * q / 2) := by
  obtain ⟨C, hC, hf⟩ := upper_geometric_root_sum_finite
  refine ⟨C, hC, ?_⟩
  intro q a hq ha hcap
  have hq0 : 0 < q := by linarith
  have hρ : 0 ≤ 1 - 1 / q := by linarith [(div_le_one hq0).mpr hq]
  have hnonneg (J : ℕ) : 0 ≤ upperGeometricRootTerm q a J := by
    unfold upperGeometricRootTerm
    positivity
  have hbound := hf q a hq (by linarith) hcap
  exact ⟨summable_of_sum_range_le hnonneg hbound,
    Real.tsum_le_of_sum_range_le hnonneg hbound⟩

end SRWTightness
