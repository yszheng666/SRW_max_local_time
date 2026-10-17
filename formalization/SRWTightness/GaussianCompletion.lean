import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Matrix

namespace SRWTightness

noncomputable def gaussianEnergy {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)
    (f c x : ι → ℝ) : ℝ :=
  (∑ i, x i ^ 2) + ∑ i, f i * (B.mulVec x i + c i) ^ 2

/-- Completing the square using the normal equation, without evaluating a determinant integral. -/
theorem gaussianEnergy_complete_square {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (f c h x : ι → ℝ)
    (hh : h = B.transpose.mulVec (fun i ↦ f i * (c i - B.mulVec h i))) :
    gaussianEnergy B f c x = gaussianEnergy B f 0 (x + h) +
      ∑ i, f i * c i * (c i - B.mulVec h i) := by
  have hx : (∑ i, x i * h i) =
      ∑ i, f i * (c i - B.mulVec h i) * B.mulVec x i := by
    change x ⬝ᵥ h = _
    exact (congrArg (fun v ↦ x ⬝ᵥ v) hh).trans
      (Matrix.dotProduct_transpose_mulVec B x (fun i ↦ f i * (c i - B.mulVec h i)))
  have hhh : (∑ i, h i ^ 2) =
      ∑ i, f i * (c i - B.mulVec h i) * B.mulVec h i := by
    have ht := Matrix.dotProduct_transpose_mulVec B h
      (fun i ↦ f i * (c i - B.mulVec h i))
    rw [← hh] at ht
    simpa only [dotProduct, pow_two] using ht
  have hnorm : (∑ i, (x i + h i) ^ 2) =
      (∑ i, x i ^ 2) + 2 * (∑ i, x i * h i) + ∑ i, h i ^ 2 := by
    calc
      _ = ∑ i, (x i ^ 2 + 2 * (x i * h i) + h i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hweighted : (∑ i, f i * (B.mulVec x i + c i) ^ 2) =
      (∑ i, f i * (B.mulVec x i + B.mulVec h i) ^ 2) +
      2 * (∑ i, f i * (c i - B.mulVec h i) * B.mulVec x i) +
      (∑ i, f i * (c i - B.mulVec h i) * B.mulVec h i) +
      ∑ i, f i * c i * (c i - B.mulVec h i) := by
    calc
      _ = ∑ i, (f i * (B.mulVec x i + B.mulVec h i) ^ 2 +
          2 * (f i * (c i - B.mulVec h i) * B.mulVec x i) +
          f i * (c i - B.mulVec h i) * B.mulVec h i +
          f i * c i * (c i - B.mulVec h i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
  unfold gaussianEnergy
  simp only [Matrix.mulVec_add, Pi.add_apply, Pi.zero_apply, add_zero]
  rw [hnorm, hweighted, hx, hhh]
  ring

end SRWTightness
