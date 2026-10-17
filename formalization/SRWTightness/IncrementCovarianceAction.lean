import SRWTightness.BrownianIncrementCovariance

open Matrix

namespace SRWTightness

/-- Brownian increment covariance acts by a weighted prefix sum of suffix sums. -/
theorem incrementCovariance_mulVec {n : ℕ} (d x : Fin n → ℝ) (i : Fin n) :
    (incrementCovariance d *ᵥ x) i =
      ∑ k : Fin n, if k ≤ i then d k * suffixSum x k.val else 0 := by
  simp only [Matrix.mulVec, dotProduct, incrementCovariance, Matrix.of_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ≤ i
  · simp only [hk, true_and, suffixSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (if k.val ≤ j.val then d k else 0) * x j =
      d k * (if k.val ≤ j.val then x j else 0)
    split <;> simp_all only [if_true, if_false, zero_mul, mul_zero]
  · simp [hk]

/-- Consecutive covariance rows differ by the intervening time gap times a suffix sum. -/
theorem incrementCovariance_mulVec_step {n : ℕ} (d x : Fin (n + 1) → ℝ) (i : Fin n) :
    (incrementCovariance d *ᵥ x) i.succ - (incrementCovariance d *ᵥ x) i.castSucc =
      d i.succ * suffixSum x i.succ.val := by
  rw [incrementCovariance_mulVec, incrementCovariance_mulVec, ← Finset.sum_sub_distrib]
  have he (k : Fin (n + 1)) :
      (if k ≤ i.succ then d k * suffixSum x k.val else 0) -
        (if k ≤ i.castSucc then d k * suffixSum x k.val else 0) =
      if k = i.succ then d i.succ * suffixSum x i.succ.val else 0 := by
    by_cases hk : k = i.succ
    · subst k
      simp [Fin.le_def]
    · have hiff : k ≤ i.succ ↔ k ≤ i.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        have hv : k.val ≠ i.val + 1 := fun h ↦ hk (Fin.ext h)
        omega
      simp [hk, hiff]
  simp_rw [he]
  simp

end SRWTightness
