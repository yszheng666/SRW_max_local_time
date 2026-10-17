import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Linarith

open MeasureTheory MvPolynomial BoundedContinuousFunction
open scoped NNReal BoundedContinuousFunction

namespace SRWTightness

noncomputable def laplaceCoordinate {ι : Type*} (i : ι) : (ι → ℝ≥0) →ᵇ ℝ where
  toFun x := Real.exp (-(x i : ℝ))
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨1, fun x y ↦ ?_⟩
    have hx0 := (Real.exp_pos (-(x i : ℝ))).le
    have hy0 := (Real.exp_pos (-(y i : ℝ))).le
    have hx1 : Real.exp (-(x i : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (x i).coe_nonneg)
    have hy1 : Real.exp (-(y i : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (y i).coe_nonneg)
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith

noncomputable def laplacePolynomialAlgebra (ι : Type*) : StarSubalgebra ℝ ((ι → ℝ≥0) →ᵇ ℝ) where
  __ := (MvPolynomial.aeval (laplaceCoordinate (ι := ι))).range
  star_mem' := by
    intro f hf
    have he : star f = f := by ext x; simp
    rw [he]
    exact hf

 theorem laplacePolynomialAlgebra_separates (ι : Type*) :
    ((laplacePolynomialAlgebra ι).map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  have hex : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  obtain ⟨i, hi⟩ := hex
  refine ⟨(laplaceCoordinate i : (ι → ℝ≥0) → ℝ), ?_, ?_⟩
  · refine ⟨(toContinuousMapStarₐ ℝ) (laplaceCoordinate i), ?_, rfl⟩
    refine ⟨laplaceCoordinate i, ?_, rfl⟩
    change laplaceCoordinate i ∈ (MvPolynomial.aeval (laplaceCoordinate (ι := ι))).range
    exact ⟨MvPolynomial.X i, MvPolynomial.aeval_X _ _⟩
  · change Real.exp (-(x i : ℝ)) ≠ Real.exp (-(y i : ℝ))
    intro he
    apply hi
    apply NNReal.coe_injective
    have ht := Real.exp_injective he
    linarith

end SRWTightness
