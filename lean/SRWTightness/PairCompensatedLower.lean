import SRWTightness.PairQuadraticSplit
import SRWTightness.PairShiftQuadratic

open Matrix

namespace SRWTightness

/-- Brownian coercivity and the two-site residual bound imply a uniform full-block lower bound. -/
theorem pairObservation_compensated_lower {n : ℕ} (last : Fin n)
    (T : Fin n → ℝ) (V : Bool → Bool → ℝ)
    (hmax : ∀ j, T j ≤ T last) (hV : V true false = V false true)
    (hB : ∀ y : Fin n → ℝ, (1 / 4 : ℝ) * (∑ j, y j ^ 2) ≤
      ∑ j, ∑ l, y j * min (T j) (T l) * y l)
    (hR : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ V false false * a ^ 2 +
      2 * V false true * a * b + V true true * b ^ 2 - T last * (a + b) ^ 2)
    (x : PairObservationIndex n → ℝ) :
    (1 / 8 : ℝ) * (∑ j, x j ^ 2) ≤
      x ⬝ᵥ (pairObservationCovarianceMatrix T (fun _ ↦ 0) V *ᵥ x) := by
  let y : Fin n → ℝ := fun j ↦ x (.inl j)
  let a := x (.inr false)
  let b := x (.inr true)
  have hsplit := pairObservation_quadratic_split T V x
  have hshift := pairEndpointShift_quadratic last T y hmax a b
  have hsite : (∑ c : Bool, ∑ d : Bool, x (.inr c) * V c d * x (.inr d)) =
      V false false * a ^ 2 + 2 * V false true * a * b + V true true * b ^ 2 := by
    simp only [Fintype.sum_bool, hV]
    dsimp only [a, b]
    ring
  rw [hsite] at hsplit
  have henergy : (1 / 4 : ℝ) * (∑ j, pairEndpointShift last y a b j ^ 2) +
      (a ^ 2 + b ^ 2) ≤
      ∑ j, ∑ l, x j * pairObservationCovarianceMatrix T (fun _ ↦ 0) V j l * x l := by
    have hb := hB (pairEndpointShift last y a b)
    have hr := hR a b
    dsimp only [y, a, b] at hshift hb hr ⊢
    linarith
  have hl := pairEndpointShift_energy_lower last y a b _ henergy
  have hnorm : (∑ j, x j ^ 2) = (∑ j, y j ^ 2) + a ^ 2 + b ^ 2 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_bool, y, a, b]
    ring
  rw [hnorm]
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hl

end SRWTightness
