import SRWTightness.SourcePairObservationCovariance

open Matrix

namespace SRWTightness

/-- Only retained average coordinates receive the discrete diagonal correction. -/
def pairObservationError {n : ℕ} (e : Fin n → ℝ) : PairObservationIndex n → ℝ
  | .inl j => e j
  | .inr _ => 0

/-- Adding the exact average corrections gives the Brownian block covariance. -/
theorem pairObservationCovarianceMatrix_compensate {n : ℕ}
    (T e : Fin n → ℝ) (V : Bool → Bool → ℝ) :
    pairObservationCovarianceMatrix T e V + Matrix.diagonal (pairObservationError e) =
      pairObservationCovarianceMatrix T (fun _ ↦ 0) V := by
  ext j l
  cases j <;> cases l <;>
    simp [pairObservationCovarianceMatrix, pairObservationError, Matrix.diagonal_apply]

theorem pairObservationError_nonneg {n : ℕ} (e : Fin n → ℝ) (he : ∀ j, 0 ≤ e j) :
    ∀ j, 0 ≤ pairObservationError e j := by
  intro j
  cases j with
  | inl j => exact he j
  | inr c => exact le_rfl

theorem pairObservationError_sum {n : ℕ} (e : Fin n → ℝ) :
    (∑ j, pairObservationError e j) = ∑ j, e j := by
  simp [Fintype.sum_sum_type, pairObservationError]

end SRWTightness
