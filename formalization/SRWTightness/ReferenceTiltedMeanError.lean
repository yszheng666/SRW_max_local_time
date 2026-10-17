import SRWTightness.ReferenceTiltedDirectionCovariance

open MeasureTheory ProbabilityTheory Set

namespace SRWTightness

/-- The actual one-mark tilted mean has a quadratic remainder in every signed direction. -/
theorem referenceMark_tilted_mean_error (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) :
    let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
    let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    |(∫ Y, H Y ∂μ.tilted (fun Y ↦ s * X Y)) - (∫ Y, H Y ∂μ) -
      s * covariance H X μ| ≤ 35389464 * L ^ 3 * (∑ z, |β z|) ^ 2 * s ^ 2 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let μ := referenceMarkLaw D K α
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  let f := fun r ↦ (∫ Y, H Y ∂μ.tilted (fun Y ↦ r * X Y)) -
    (∫ Y, H Y ∂μ) - r * covariance H X μ
  have hseg (r : ℝ) (hr : r ∈ uIcc 0 s) : |r| * (∑ z, |β z|) < 1 / (8 * L) := by
    have ha : |r| ≤ |s| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
    exact (mul_le_mul_of_nonneg_right ha (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))).trans_lt hs
  have hd (r : ℝ) (hr : r ∈ uIcc 0 s) : HasDerivAt f
      (covariance H X (μ.tilted (fun Y ↦ r * X Y)) - covariance H X μ) r := by
    have hm : HasDerivAt (fun t ↦ ∫ Y, H Y ∂μ.tilted (fun Y ↦ t * X Y))
        (covariance H X (μ.tilted (fun Y ↦ r * X Y))) r :=
      referenceMark_hasDerivAt_tilted_mean D K hKD α hα hcap w hw β L hL hG r (hseg r hr)
    have hh : HasDerivAt f
        (covariance H X (μ.tilted (fun Y ↦ r * X Y)) - 1 * covariance H X μ) r :=
      (hm.sub_const (∫ Y, H Y ∂μ)).sub ((hasDerivAt_id r).mul_const (covariance H X μ))
    simpa only [one_mul] using hh
  have hb (r : ℝ) (hr : r ∈ uIcc 0 s) :
      ‖deriv f r‖ ≤ 35389464 * L ^ 3 * (∑ z, |β z|) ^ 2 * |s| := by
    rw [(hd r hr).deriv, Real.norm_eq_abs]
    have hh := referenceMark_tilted_direction_covariance_drift D K hKD α hα hcap
      w hw hw1 β L hL hαL hG r (hseg r hr)
    refine hh.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun r hr ↦ (hd r hr).differentiableAt) hb (convex_uIcc 0 s)
    left_mem_uIcc right_mem_uIcc
  have he : (35389464 * L ^ 3 * (∑ z, |β z|) ^ 2 * |s|) * |s| =
      35389464 * L ^ 3 * (∑ z, |β z|) ^ 2 * s ^ 2 := by
    rw [mul_assoc, ← pow_two, sq_abs]
  simpa only [f, zero_mul, tilted_const, sub_self, sub_zero, Real.norm_eq_abs, he] using hh

end SRWTightness
