import SRWTightness.ConvexOuterCutoff

namespace SRWTightness

theorem quadraticCutoffSlope_linear_bound (s : ℝ) (hs : 0 ≤ s) :
    |quadraticCutoffSlope s| ≤ 4 * s := by
  have hn := (quadraticCutoffSlope_bounds s).2
  rw [abs_of_nonpos hn]
  unfold quadraticCutoffSlope
  split_ifs <;> linarith

theorem scaledQuadraticCutoff_deriv_linear_bound (ε s : ℝ) (hε : 0 < ε)
    (hs : 0 ≤ s) : |deriv (scaledQuadraticCutoff ε) s| ≤ (4 / ε ^ 2) * s := by
  rw [scaledQuadraticCutoff_deriv, abs_div, abs_of_pos hε]
  have h := div_le_div_of_nonneg_right
    (quadraticCutoffSlope_linear_bound (s / ε) (div_nonneg hs hε.le)) hε.le
  exact h.trans_eq (by field_simp)

/-- Uniform variation of the actual outer cutoff derivative, with the smoothing constant eight. -/
theorem convexOuterCutoff_fderiv_dist {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (x y : E) :
    ‖fderiv ℝ (convexOuterCutoff K ε) x - fderiv ℝ (convexOuterCutoff K ε) y‖ ≤
      (8 / ε ^ 2) * ‖x - y‖ := by
  let d := fun z ↦ Metric.infDist z K
  let D := fderiv ℝ d
  let a := deriv (scaledQuadraticCutoff ε)
  let F := fderiv ℝ (convexOuterCutoff K ε)
  have hf (z : E) : F z = a (d z) • D z := by
    simpa only [F, a, d, D, scaledQuadraticCutoff_deriv] using
      (convexOuterCutoff_hasFDerivAt K hne hcomplete hconvex ε hε z).fderiv
  have hd (z w : E) : |d z - d w| ≤ ‖z - w‖ := by
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs, d] using
      (Metric.lipschitz_infDist_pt (s := K)).dist_le_mul z w
  have hc : 0 ≤ 4 / ε ^ 2 := by positivity
  have hz (z : E) (hz : d z = 0) : F z = 0 :=
    (convexOuterCutoff_hasFDerivAt_zero K hne hcomplete hconvex ε hε z hz).fderiv
  have hn (z : E) (hz : 0 < d z) : ‖D z‖ = 1 :=
    convexDistance_fderiv_norm K hne hcomplete hconvex z hz
  have hb (z : E) : ‖F z‖ ≤ (4 / ε ^ 2) * d z := by
    by_cases h : d z = 0
    · rw [hz z h, norm_zero, h, mul_zero]
    · have hp : 0 < d z := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm h)
      rw [hf, norm_smul, hn z hp, mul_one, Real.norm_eq_abs]
      exact scaledQuadraticCutoff_deriv_linear_bound ε (d z) hε Metric.infDist_nonneg
  have ordered (z w : E) (hwz : d w ≤ d z) :
      ‖F z - F w‖ ≤ (8 / ε ^ 2) * ‖z - w‖ := by
    by_cases hw : d w = 0
    · rw [hz w hw, sub_zero]
      have hdist : d z ≤ ‖z - w‖ := by
        simpa only [hw, sub_zero, abs_of_nonneg (show 0 ≤ d z from Metric.infDist_nonneg)] using hd z w
      have hh := (hb z).trans (mul_le_mul_of_nonneg_left hdist hc)
      have hscale : 4 / ε ^ 2 ≤ 8 / ε ^ 2 := by
        apply div_le_div_of_nonneg_right (by norm_num) (sq_nonneg ε)
      exact hh.trans (mul_le_mul_of_nonneg_right hscale (norm_nonneg _))
    · have hwp : 0 < d w := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hw)
      have hzp : 0 < d z := hwp.trans_le hwz
      have hfirst : |a (d z) - a (d w)| ≤ (4 / ε ^ 2) * ‖z - w‖ :=
        (scaledQuadraticCutoff_deriv_dist ε (d z) (d w) hε).trans
          (mul_le_mul_of_nonneg_left (hd z w) hc)
      have hgrad : ‖D z - D w‖ ≤ ‖z - w‖ / d w := by
        have hh := convexDistance_fderiv_sub_le K hne hcomplete hconvex z w hzp hwp
        change ‖D z - D w‖ ≤ ‖z - w‖ / min (d z) (d w) at hh
        simpa only [min_eq_right hwz] using hh
      have hsecond : |a (d w)| * ‖D z - D w‖ ≤ (4 / ε ^ 2) * ‖z - w‖ := by
        have hh := mul_le_mul
          (scaledQuadraticCutoff_deriv_linear_bound ε (d w) hε hwp.le)
          hgrad (norm_nonneg _) (mul_nonneg hc hwp.le)
        exact hh.trans_eq (by field_simp)
      have ht := norm_sub_le_norm_sub_add_norm_sub (a (d z) • D z) (a (d w) • D z) (a (d w) • D w)
      rw [← sub_smul, ← smul_sub, norm_smul, norm_smul, hn z hzp, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs] at ht
      rw [hf z, hf w]
      have he : (8 / ε ^ 2) * ‖z - w‖ =
          (4 / ε ^ 2) * ‖z - w‖ + (4 / ε ^ 2) * ‖z - w‖ := by ring
      rw [he]
      exact ht.trans (add_le_add hfirst hsecond)
  rcases le_total (d y) (d x) with h | h
  · exact ordered x y h
  · simpa only [norm_sub_rev] using ordered y x h

/-- The derivative is globally Lipschitz with the explicit inverse-square scale. -/
theorem convexOuterCutoff_fderiv_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith ⟨8 / ε ^ 2, by positivity⟩ (fderiv ℝ (convexOuterCutoff K ε)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖fderiv ℝ (convexOuterCutoff K ε) x -
    fderiv ℝ (convexOuterCutoff K ε) y‖ ≤ (8 / ε ^ 2) * ‖x - y‖
  exact convexOuterCutoff_fderiv_dist K hne hcomplete hconvex ε hε x y

/-- Both the outer cutoff and its derivative are continuous on the whole space. -/
theorem convexOuterCutoff_continuous_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    Continuous (convexOuterCutoff K ε) ∧
      Continuous (fderiv ℝ (convexOuterCutoff K ε)) := by
  constructor
  · exact continuous_iff_continuousAt.mpr (fun x ↦
      (convexOuterCutoff_hasFDerivAt K hne hcomplete hconvex ε hε x).continuousAt)
  · exact (convexOuterCutoff_fderiv_lipschitz K hne hcomplete hconvex ε hε).continuous

end SRWTightness
