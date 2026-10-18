import SRWTightness.IncrementCovarianceInverseAction

open Matrix

namespace SRWTightness

/-- Interior inverse coordinates are differences of two neighboring normalized increments. -/
theorem incrementCovariance_inverse_coordinate {n : ℕ} (d y : Fin (n + 1) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hd : ∀ i, δ ≤ d i) (i : Fin n) :
    ((incrementCovariance d)⁻¹ *ᵥ y) i.castSucc =
      suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) i.val -
        (y i.succ - y i.castSucc) / d i.succ := by
  have hh := suffixSum_step ((incrementCovariance d)⁻¹ *ᵥ y) i.castSucc
  have hs := incrementCovariance_inverse_suffix_step d y δ hδ hd i
  change suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) (i.val + 1) = _ at hs
  simp only [Fin.val_castSucc] at hh
  rw [hs] at hh
  linarith

/-- The final inverse coordinate is exactly the final nonzero suffix sum. -/
theorem incrementCovariance_inverse_coordinate_last {n : ℕ} (d y : Fin (n + 1) → ℝ) :
    ((incrementCovariance d)⁻¹ *ᵥ y) (Fin.last n) =
      suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) n := by
  have hh := suffixSum_step ((incrementCovariance d)⁻¹ *ᵥ y) (Fin.last n)
  simpa using hh.symm

/-- Every inverse coordinate square is controlled by the two adjacent suffix squares. -/
theorem incrementCovariance_inverse_coordinate_sq {n : ℕ} (d y : Fin n → ℝ) (i : Fin n) :
    ((incrementCovariance d)⁻¹ *ᵥ y) i ^ 2 ≤
      2 * suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) i.val ^ 2 +
      2 * suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) (i.val + 1) ^ 2 := by
  have hh := suffixSum_step ((incrementCovariance d)⁻¹ *ᵥ y) i
  rw [show ((incrementCovariance d)⁻¹ *ᵥ y) i =
    suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) i.val -
    suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) (i.val + 1) by linarith]
  nlinarith [sq_nonneg (suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) i.val +
    suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) (i.val + 1))]

end SRWTightness
