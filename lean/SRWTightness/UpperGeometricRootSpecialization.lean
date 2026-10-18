import SRWTightness.UpperGeometricRootSum

namespace SRWTightness

/-- A bounded slope error times the return scale yields the source spatial cancellation factor. -/
theorem upper_geometric_root_specialization :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ k : ℕ, ∀ a δ : ℝ,
      1 / 2 ≤ a → a ≤ 3 → 0 ≤ δ → a ≤ 2 + δ → δ * (k + K) ≤ 1 →
      Summable (upperGeometricRootTerm (k + K) a) ∧
        (∑' J : ℕ, upperGeometricRootTerm (k + K) a J) ≤
          (C * K ^ 2 * Real.exp (2 * K + 5 / 2)) *
            ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k) := by
  obtain ⟨C, hC, hsum⟩ := upper_geometric_root_sum_bound
  refine ⟨C, hC, ?_⟩
  intro K hK k a δ ha ha3 hδ had hδq
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hq : 1 ≤ (k : ℝ) + K := by linarith
  obtain ⟨hs, hb⟩ := hsum (k + K) a hq ha ha3
  refine ⟨hs, hb.trans ?_⟩
  have ha2 : a ^ 2 ≤ 4 + 5 * δ := by
    by_cases h : a ≤ 2
    · nlinarith
    · have hp : 0 ≤ (3 - a) * (a - 2) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  have hexp : a ^ 2 * (k + K) / 2 ≤ 2 * k + (2 * K + 5 / 2) := by
    have hm := mul_le_mul_of_nonneg_right ha2 (by linarith : 0 ≤ (k : ℝ) + K)
    nlinarith
  have hqbound : (k : ℝ) + K ≤ K * (k + 1) := by
    nlinarith [mul_nonneg hk (by linarith : 0 ≤ K - 1)]
  have hsq : ((k : ℝ) + K) ^ 2 ≤ K ^ 2 * ((k : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (K * (k + 1) - (k + K))]
  calc
    _ ≤ C * (K ^ 2 * ((k : ℝ) + 1) ^ 2) *
        Real.exp (2 * k + (2 * K + 5 / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq hC.le)
        (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

end SRWTightness
