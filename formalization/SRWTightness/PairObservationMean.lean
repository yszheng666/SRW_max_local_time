import SRWTightness.SourcePairObservationCovariance

namespace SRWTightness

/-- The Gaussian comparison mean has a positive correction only at the last average. -/
theorem pairObservation_average_mean {n : ℕ} (last : Fin n)
    (T e : Fin n → ℝ) (V : Bool → Bool → ℝ) (hmax : ∀ j, T j ≤ T last) (j : Fin n) :
    (∑ l, pairObservationTilt last l * pairObservationCovarianceMatrix T e V (.inl j) l) =
      2 * T j + if j = last then 2 * e j else 0 := by
  unfold pairObservationTilt
  rw [pairTiltWeight_sum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    pairObservationCovarianceMatrix, min_eq_left (hmax j)]
  split <;> ring

/-- In particular, the drift correction cannot loosen the flat prefix barrier. -/
theorem pairObservation_average_mean_ge {n : ℕ} (last : Fin n)
    (T e : Fin n → ℝ) (V : Bool → Bool → ℝ) (hmax : ∀ j, T j ≤ T last)
    (he : ∀ j, 0 ≤ e j) (j : Fin n) :
    2 * T j ≤ ∑ l, pairObservationTilt last l *
      pairObservationCovarianceMatrix T e V (.inl j) l := by
  rw [pairObservation_average_mean last T e V hmax j]
  split <;> linarith [he j]

end SRWTightness
