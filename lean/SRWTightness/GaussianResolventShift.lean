import SRWTightness.GaussianCompletion
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

namespace SRWTightness

noncomputable def quadraticResolvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (f : ι → ℝ) : Matrix ι ι ℝ :=
  1 + (B * B) * Matrix.diagonal f

noncomputable def gaussianShiftVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (f c : ι → ℝ) : ι → ℝ :=
  B.mulVec ((Matrix.diagonal f).mulVec ((quadraticResolvent B f)⁻¹.mulVec c))

 theorem gaussianShiftVector_residual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (f c : ι → ℝ) (hC : IsUnit (quadraticResolvent B f)) :
    c - B.mulVec (gaussianShiftVector B f c) = (quadraticResolvent B f)⁻¹.mulVec c := by
  let t := (quadraticResolvent B f)⁻¹.mulVec c
  have he : (quadraticResolvent B f).mulVec t = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hC), Matrix.one_mulVec]
  have hx : t + B.mulVec (gaussianShiftVector B f c) = c := by
    simpa only [quadraticResolvent, Matrix.add_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, gaussianShiftVector, t] using he
  exact (congrArg (fun v ↦ v - B.mulVec (gaussianShiftVector B f c)) hx.symm).trans
    (add_sub_cancel_right _ _)

 theorem gaussianShiftVector_normal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.transpose = B) (f c : ι → ℝ)
    (hC : IsUnit (quadraticResolvent B f)) :
    gaussianShiftVector B f c = B.transpose.mulVec
      (fun i ↦ f i * (c i - B.mulVec (gaussianShiftVector B f c) i)) := by
  have ht := gaussianShiftVector_residual B f c hC
  rw [hB]
  have he : (fun i ↦ f i * (c i - B.mulVec (gaussianShiftVector B f c) i)) =
      (Matrix.diagonal f).mulVec ((quadraticResolvent B f)⁻¹.mulVec c) := by
    funext i
    rw [Matrix.mulVec_diagonal, ← ht]
    rfl
  rw [he]
  rfl

 theorem gaussianEnergy_resolvent_complete {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.transpose = B) (f c x : ι → ℝ)
    (hC : IsUnit (quadraticResolvent B f)) :
    gaussianEnergy B f c x =
      gaussianEnergy B f 0 (x + gaussianShiftVector B f c) +
        ∑ i, f i * c i * ((quadraticResolvent B f)⁻¹.mulVec c) i := by
  rw [gaussianEnergy_complete_square B f c (gaussianShiftVector B f c) x
    (gaussianShiftVector_normal B hB f c hC)]
  have ht := gaussianShiftVector_residual B f c hC
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← ht]
  rfl

end SRWTightness
