import SRWTightness.IncrementCovarianceInverseAction
import SRWTightness.SuffixCoordinateMoment

open MeasureTheory Matrix

namespace SRWTightness

/-- Normalized observation increment moments control every actual inverse covariance coordinate. -/
theorem incrementCovariance_inverse_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (d : Fin (n + 1) → ℝ) (hd : ∀ i, 1 ≤ d i)
    (Y : Ω → Fin (n + 1) → ℝ) (hY : ∀ i, Measurable (fun ω ↦ Y ω i))
    (M : ℝ) (hM : 0 ≤ M)
    (hfirst : Integrable (fun ω ↦ (Y ω 0 / d 0) ^ 2) μ ∧
      (∫ ω, (Y ω 0 / d 0) ^ 2 ∂μ) ≤ M)
    (hstep : ∀ i : Fin n,
      Integrable (fun ω ↦ ((Y ω i.succ - Y ω i.castSucc) / d i.succ) ^ 2) μ ∧
      (∫ ω, ((Y ω i.succ - Y ω i.castSucc) / d i.succ) ^ 2 ∂μ) ≤ M)
    (i : Fin (n + 1)) :
    Integrable (fun ω ↦ ((incrementCovariance d)⁻¹ *ᵥ Y ω) i ^ 2) μ ∧
      (∫ ω, ((incrementCovariance d)⁻¹ *ᵥ Y ω) i ^ 2 ∂μ) ≤ 4 * M := by
  apply suffix_coordinate_moment μ (fun ω ↦ (incrementCovariance d)⁻¹ *ᵥ Y ω) _ M hM _ i
  · intro j
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  · intro k hk
    by_cases hlast : k = n + 1
    · subst k
      simpa only [suffixSum_terminal, zero_pow (by omega : 2 ≠ 0), integral_zero]
        using (show Integrable (fun _ : Ω ↦ (0 : ℝ)) μ ∧ 0 ≤ M from ⟨integrable_zero _ _ _, hM⟩)
    · have hkn : k < n + 1 := by omega
      cases k with
      | zero =>
          simpa only [incrementCovariance_inverse_suffix_zero d _ 1 (by norm_num) hd] using hfirst
      | succ k =>
          have hks : k < n := by omega
          have he (ω : Ω) := incrementCovariance_inverse_suffix_step d (Y ω) 1
            (by norm_num) hd (⟨k, hks⟩ : Fin n)
          simp only [Fin.val_succ, Fin.val_mk] at he
          simp_rw [he]
          exact hstep ⟨k, hks⟩

end SRWTightness
