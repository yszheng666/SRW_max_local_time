import SRWTightness.ReferenceTiltedCovarianceBound
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory ProbabilityTheory Set

namespace SRWTightness

/-- Quantitative covariance stability under an actual signed reference-mark tilt. -/
theorem referenceMark_tilted_covariance_drift (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w v : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hv : ∀ z, 0 ≤ v z)
    (hw1 : ∑ z, w z = 1) (hv1 : ∑ z, v z = 1) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) :
    let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
    let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
    let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    |covariance H J (μ.tilted (fun Y ↦ s * X Y)) - covariance H J μ| ≤
      35389464 * L ^ 3 * (∑ z, |β z|) * |s| := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  let μ := referenceMarkLaw D K α
  let f := fun t ↦ covariance H J (μ.tilted (fun Y ↦ t * X Y))
  have hseg (r : ℝ) (hr : r ∈ uIcc 0 s) : |r| * (∑ z, |β z|) < 1 / (8 * L) := by
    have habs : |r| ≤ |s| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
    exact (mul_le_mul_of_nonneg_right habs (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))).trans_lt hs
  have hdiff (r : ℝ) (hr : r ∈ uIcc 0 s) : DifferentiableAt ℝ f r :=
    (referenceMark_hasDerivAt_tilted_covariance D K hKD α hα hcap w v hw hv hw1 hv1
      β L hL hG r (hseg r hr)).differentiableAt
  have hb (r : ℝ) (hr : r ∈ uIcc 0 s) : ‖deriv f r‖ ≤ 35389464 * L ^ 3 * (∑ z, |β z|) := by
    simpa only [Real.norm_eq_abs] using referenceMark_tilted_covariance_deriv_bound
      D K hKD α hα hcap w v hw hv hw1 hv1 β L hL hαL hG r (hseg r hr)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_uIcc 0 s)
    left_mem_uIcc right_mem_uIcc
  simpa only [f, zero_mul, tilted_const, sub_zero, Real.norm_eq_abs] using hh

end SRWTightness
