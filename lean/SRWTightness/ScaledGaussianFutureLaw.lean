import SRWTightness.ScaledGaussianFutureMoments

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A scaled Brownian increment segment has the exact Brownian path law for its elapsed duration. -/
theorem scaled_gaussian_future_path_law (T r t : ℝ) (hT : 0 < T)
    (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ T) :
    gaussianCoefficientLaw.map (fun ω (u : Set.Icc (0 : ℝ) (t - r)) ↦
      Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) -
        Real.sqrt T * gaussianDyadicPath ω (r / T)) =
    gaussianCoefficientLaw.map (fun ω (u : Set.Icc (0 : ℝ) (t - r)) ↦
      Real.sqrt (t - r) * gaussianDyadicPath ω (u / (t - r))) := by
  have hd : 0 < t - r := sub_pos.mpr hrt
  let j : Set.Icc (0 : ℝ) (t - r) → Set.Icc (0 : ℝ) r ⊕ Set.Icc r t :=
    fun u ↦ Sum.inr ⟨r + u, by linarith [u.property.1], by linarith [u.property.2]⟩
  have hg := (scaled_gaussian_past_future_gaussian T r t hT hr hrt.le ht).comp_right j
  apply gaussian_cross_space_process_law_eq gaussianCoefficientLaw gaussianCoefficientLaw _ _
    hg (scaled_gaussian_path_process (t - r) hd)
  · exact measurable_pi_lambda _ (fun u ↦
      (measurable_const.mul (gaussianDyadicPath_measurable _)).sub
        (measurable_const.mul (gaussianDyadicPath_measurable _)))
  · exact measurable_pi_lambda _ (fun u ↦
      measurable_const.mul (gaussianDyadicPath_measurable _))
  · intro u
    change (∫ ω, Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) -
      Real.sqrt T * gaussianDyadicPath ω (r / T) ∂gaussianCoefficientLaw) = _
    rw [scaled_gaussian_increment_mean T r (r + u) hT hr (by linarith [u.property.1])
      (by linarith [u.property.2]), integral_const_mul,
      (gaussianPath_eval_hasLaw (u / (t - r)) (div_nonneg u.property.1 hd.le)
        ((div_le_one hd).mpr u.property.2)).integral_eq, integral_id_gaussianReal, mul_zero]
  · intro u v
    change cov[fun ω ↦ Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) -
        Real.sqrt T * gaussianDyadicPath ω (r / T),
      fun ω ↦ Real.sqrt T * gaussianDyadicPath ω ((r + v) / T) -
        Real.sqrt T * gaussianDyadicPath ω (r / T); gaussianCoefficientLaw] = _
    rw [scaled_gaussian_future_covariance T r u v hT hr u.property.1 v.property.1
      (by linarith [u.property.2]) (by linarith [v.property.2]),
      scaled_gaussian_path_covariance (t - r) u v hd u.property.1 u.property.2
        v.property.1 v.property.2]

/-- Elapsed-time scaled Brownian future increments are independent of the whole past. -/
theorem scaled_gaussian_elapsed_future_indep_past (T r t : ℝ) (hT : 0 < T)
    (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    IndepFun (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T))
      (fun ω (u : Set.Icc (0 : ℝ) (t - r)) ↦
        Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) -
          Real.sqrt T * gaussianDyadicPath ω (r / T)) gaussianCoefficientLaw := by
  let H : (Set.Icc r t → ℝ) → (Set.Icc (0 : ℝ) (t - r) → ℝ) :=
    fun f u ↦ f ⟨r + u, by linarith [u.property.1], by linarith [u.property.2]⟩
  have hH : Measurable H := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  exact (scaled_gaussian_future_indep_past T r t hT hr hrt ht).comp measurable_id hH

end SRWTightness
