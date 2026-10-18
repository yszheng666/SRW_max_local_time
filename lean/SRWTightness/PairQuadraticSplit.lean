import SRWTightness.SourcePairObservationCovariance
import Mathlib.Tactic.Ring

open Matrix

namespace SRWTightness

/-- The compensated pair quadratic form splits into its average, cross and site blocks. -/
theorem pairObservation_quadratic_split {n : ℕ} (T : Fin n → ℝ)
    (V : Bool → Bool → ℝ) (x : PairObservationIndex n → ℝ) :
    (∑ j, ∑ l, x j * pairObservationCovarianceMatrix T (fun _ ↦ 0) V j l * x l) =
      (∑ j : Fin n, ∑ l : Fin n, x (.inl j) * min (T j) (T l) * x (.inl l)) +
      2 * (x (.inr false) + x (.inr true)) * (∑ j : Fin n, x (.inl j) * T j) +
      (∑ c : Bool, ∑ d : Bool, x (.inr c) * V c d * x (.inr d)) := by
  simp only [Fintype.sum_sum_type, pairObservationCovarianceMatrix, ite_self, sub_zero,
    Finset.sum_add_distrib, Fintype.sum_bool]
  have hleft (j : Fin n) (c : Bool) :
      x (.inl j) * T j * x (.inr c) = x (.inr c) * (x (.inl j) * T j) := by ring
  have hright (j : Fin n) (c : Bool) :
      x (.inr c) * T j * x (.inl j) = x (.inr c) * (x (.inl j) * T j) := by ring
  simp_rw [hleft, hright]
  simp only [← Finset.mul_sum]
  ring

end SRWTightness
