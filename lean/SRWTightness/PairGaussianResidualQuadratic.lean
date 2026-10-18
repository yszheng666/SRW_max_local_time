import SRWTightness.PairQuadraticSplit
import SRWTightness.PairShiftQuadratic
import SRWTightness.PairResidualQuadratic

open Matrix

namespace SRWTightness

/-- The full compensated pair covariance has the exact independent endpoint-residual energy. -/
theorem pair_gaussian_residual_quadratic {n : ℕ} (last : Fin n)
    (T : Fin n → ℝ) (V : Matrix Bool Bool ℝ)
    (hmax : ∀ j, T j ≤ T last) (hV : V true false = V false true)
    (x : PairObservationIndex n → ℝ) :
    x ⬝ᵥ (pairObservationCovarianceMatrix T (fun _ ↦ 0) V *ᵥ x) =
      pairEndpointShift last (fun j ↦ x (.inl j)) (x (.inr false)) (x (.inr true)) ⬝ᵥ
        ((fun j l ↦ min (T j) (T l)) *ᵥ
          pairEndpointShift last (fun j ↦ x (.inl j)) (x (.inr false)) (x (.inr true))) +
      (![x (.inr false), x (.inr true)] : Fin 2 → ℝ) ⬝ᵥ
        (pairResidualMatrix (V false false) (V true true) (V false true) (T last) *ᵥ
          ![x (.inr false), x (.inr true)]) := by
  have hs := pairObservation_quadratic_split T V x
  have hh := pairEndpointShift_quadratic last T (fun j ↦ x (.inl j)) hmax
    (x (.inr false)) (x (.inr true))
  rw [pairResidualMatrix_quadratic]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hv : (∑ c : Bool, ∑ d : Bool, x (.inr c) * V c d * x (.inr d)) =
      V false false * x (.inr false) ^ 2 +
        2 * V false true * x (.inr false) * x (.inr true) +
        V true true * x (.inr true) ^ 2 := by
    simp only [Fintype.sum_bool, hV]
    ring
  rw [hv] at hs
  simp only [mul_assoc] at hs hh
  linarith

/-- Nonnegative Brownian block energy and positive residual imply a valid full covariance. -/
theorem pair_gaussian_residual_posSemidef {n : ℕ} (last : Fin n)
    (T : Fin n → ℝ) (V : Matrix Bool Bool ℝ)
    (hmax : ∀ j, T j ≤ T last) (hV : V true false = V false true)
    (hB : ∀ x : Fin n → ℝ, 0 ≤ ∑ j, ∑ l, x j * min (T j) (T l) * x l)
    (hR : (pairResidualMatrix (V false false) (V true true) (V false true)
      (T last)).PosSemidef) :
    (pairObservationCovarianceMatrix T (fun _ ↦ 0) V).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · ext i j
    cases i with
    | inl i => cases j <;> simp [pairObservationCovarianceMatrix, min_comm]
    | inr c =>
      cases j with
      | inl j => simp [pairObservationCovarianceMatrix]
      | inr d => cases c <;> cases d <;> simp [pairObservationCovarianceMatrix, hV]
  · intro x
    simp only [star_trivial]
    rw [pair_gaussian_residual_quadratic last T V hmax hV]
    apply add_nonneg
    · simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
        hB (pairEndpointShift last (fun j ↦ x (.inl j)) (x (.inr false)) (x (.inr true)))
    · simpa only [star_trivial] using
        hR.dotProduct_mulVec_nonneg (![x (.inr false), x (.inr true)] : Fin 2 → ℝ)

end SRWTightness
