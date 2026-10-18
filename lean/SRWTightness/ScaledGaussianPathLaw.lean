import SRWTightness.MeasurableBrownianReconstruction

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Scaling the actual unit Gaussian path gives the Brownian Gaussian process on any duration. -/
theorem scaled_gaussian_path_process (T : ℝ) (hT : 0 < T) :
    IsGaussianProcess (fun t : Set.Icc (0 : ℝ) T ↦ fun ω ↦
      Real.sqrt T * gaussianDyadicPath ω (t / T)) gaussianCoefficientLaw := by
  let f : Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) 1 := fun t ↦
    ⟨t.val / T, div_nonneg t.property.1 hT.le, (div_le_one hT).mpr t.property.2⟩
  exact (gaussianPath_unit_gaussianProcess.comp_right f).smul (fun _ ↦ Real.sqrt T)

/-- The scaled actual Gaussian path has the exact Brownian covariance. -/
theorem scaled_gaussian_path_covariance (T s t : ℝ) (hT : 0 < T)
    (hs : 0 ≤ s) (hsT : s ≤ T) (ht : 0 ≤ t) (htT : t ≤ T) :
    cov[fun ω ↦ Real.sqrt T * gaussianDyadicPath ω (s / T),
      fun ω ↦ Real.sqrt T * gaussianDyadicPath ω (t / T);
      gaussianCoefficientLaw] = min s t := by
  rw [covariance_const_mul_left, covariance_const_mul_right,
    gaussianPath_covariance (s / T) (t / T) (div_nonneg hs hT.le)
      ((div_le_one hT).mpr hsT) (div_nonneg ht hT.le) ((div_le_one hT).mpr htT)]
  have hm : min (s / T) (t / T) = min s t / T := by
    rcases le_total s t with h | h
    · rw [min_eq_left h, min_eq_left ((div_le_div_iff_of_pos_right hT).mpr h)]
    · rw [min_eq_right h, min_eq_right ((div_le_div_iff_of_pos_right hT).mpr h)]
  rw [hm, ← mul_assoc, Real.mul_self_sqrt hT.le]
  field_simp

/-- The actual scaled path has the exact independent endpoint/bridge reconstruction law. -/
theorem scaled_gaussian_endpoint_bridge_law (T : ℝ) (hT : 0 < T) :
    gaussianCoefficientLaw.map (fun ω ↦
      (Real.sqrt T * gaussianDyadicPath ω (T / T),
        fun t : Set.Icc (0 : ℝ) T ↦ Real.sqrt T * gaussianDyadicPath ω (t / T))) =
      ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).map
        (fun p ↦ (p.1, fun t : Set.Icc (0 : ℝ) T ↦
          endpointBrownianBridge T p.1 t p.2)) := by
  apply measurable_brownian_endpoint_bridge_law gaussianCoefficientLaw
    (fun t ω ↦ Real.sqrt T * gaussianDyadicPath ω (t / T)) T hT
    (scaled_gaussian_path_process T hT)
  · intro t
    exact measurable_const.mul (gaussianDyadicPath_measurable _)
  · intro t
    rw [integral_const_mul,
      (gaussianPath_eval_hasLaw (t / T) (div_nonneg t.property.1 hT.le)
        ((div_le_one hT).mpr t.property.2)).integral_eq, integral_id_gaussianReal, mul_zero]
  · intro s t
    exact scaled_gaussian_path_covariance T s t hT s.property.1 s.property.2
      t.property.1 t.property.2

end SRWTightness
