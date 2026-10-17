import SRWTightness.RotatedDiagonalIteratedIntegral
import SRWTightness.NormalizedCosineIntegral
import SRWTightness.DiagonalAbsoluteQuotient
import SRWTightness.SineNonzeroAE

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- The actual diagonal potential reduces to a single angular quotient integral. -/
theorem potentialKernel_diagonal_integral (n : ℕ) :
    potentialKernel ((n : ℤ), (n : ℤ)) =
      (1 / (2 * Real.pi)) * ∫ u in 0..2 * Real.pi, diagonalAbsoluteQuotient n u := by
  refine (potentialKernel_diagonal_rotated n).trans ?_
  refine (congrArg (fun x : ℝ ↦ (4 * Real.pi ^ 2)⁻¹ * x)
    (rotated_diagonal_iterated_integral n)).trans ?_
  have hi (u : ℝ) (hu : Real.sin u ≠ 0) :
      (∫ v in 0..2 * Real.pi,
        (1 - Real.cos (2 * (n : ℝ) * u)) / (1 - Real.cos u * Real.cos v)) =
      (2 * Real.pi) * diagonalAbsoluteQuotient n u := by
    calc
      _ = (1 - Real.cos (2 * (n : ℝ) * u)) *
          ∫ v in 0..2 * Real.pi, 1 / (1 - Real.cos u * Real.cos v) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v hv
        ring
      _ = _ := by
        rw [angular_cosine_integral u hu]
        unfold diagonalAbsoluteQuotient
        ring
  have he : (∫ u in 0..2 * Real.pi, ∫ v in 0..2 * Real.pi,
      (1 - Real.cos (2 * (n : ℝ) * u)) / (1 - Real.cos u * Real.cos v)) =
      ∫ u in 0..2 * Real.pi, (2 * Real.pi) * diagonalAbsoluteQuotient n u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [sine_nonzero_ae] with u hu hmem
    exact hi u hu
  rw [he, intervalIntegral.integral_const_mul]
  field_simp
  <;> ring

/-- Exact diagonal values of the planar SRW potential kernel. -/
theorem potentialKernel_diagonal_exact (n : ℕ) :
    potentialKernel ((n : ℤ), (n : ℤ)) =
      (4 / Real.pi) * ∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1) := by
  rw [potentialKernel_diagonal_integral, diagonalAbsoluteQuotient_integral]
  ring

end SRWTightness
