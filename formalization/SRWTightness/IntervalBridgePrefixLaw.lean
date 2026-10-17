import SRWTightness.IntervalBridgePrefixResidual
import SRWTightness.GaussianProcessLawUniqueness

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The centered prefix bridge is independent of the bridge's intermediate value. -/
theorem interval_bridge_prefix_independent (T r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T) :
    IndepFun (fun ω (t : Set.Icc (0 : ℝ) r) ↦ intervalBridgePrefixResidual T r t ω)
      (actualIntervalBridge T r) gaussianCoefficientLaw := by
  have hm (u : Set.Icc (0 : ℝ) T) :=
    ((actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval u).memLp_two
  have hc (t : Set.Icc (0 : ℝ) r) :
      cov[intervalBridgePrefixResidual T r t, actualIntervalBridge T r;
        gaussianCoefficientLaw] = 0 := by
    unfold intervalBridgePrefixResidual
    rw [covariance_fun_sub_left (hm ⟨t, t.property.1, t.property.2.trans hrT⟩)
      ((hm ⟨r, hr.le, hrT⟩).const_mul _) (hm ⟨r, hr.le, hrT⟩),
      covariance_const_mul_left,
      actualIntervalBridge_covariance T t r hT t.property.1 (t.property.2.trans hrT) hr.le hrT,
      actualIntervalBridge_covariance T r r hT hr.le hrT hr.le hrT,
      min_eq_left t.property.2, min_self]
    field_simp
    <;> ring
  have hi := IsGaussianProcess.indepFun_of_covariance_eq_zero
    (interval_bridge_prefix_joint_gaussian T r hT hr.le hrT)
    (fun t ↦ (intervalBridgePrefixResidual_measurable T r t).aemeasurable)
    (fun _ ↦ (actualIntervalBridge_measurable T r).aemeasurable) (fun t _ ↦ hc t)
  exact hi.comp measurable_id (measurable_pi_apply ())

/-- The entire centered prefix residual is exactly a bridge of the shorter duration. -/
theorem interval_bridge_prefix_path_law (T r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T) :
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) r) ↦ intervalBridgePrefixResidual T r t ω) =
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) r) ↦ actualIntervalBridge r t ω) := by
  apply gaussian_process_law_eq_of_mean_covariance gaussianCoefficientLaw _ _
    ((interval_bridge_prefix_joint_gaussian T r hT hr.le hrT).comp_right Sum.inl)
    (actualIntervalBridge_gaussian r hr)
  · exact measurable_pi_lambda _ (fun t ↦ intervalBridgePrefixResidual_measurable T r t)
  · exact measurable_pi_lambda _ (fun t ↦ actualIntervalBridge_measurable r t)
  · intro t
    simp only [Function.comp_def, Sum.elim_inl]
    rw [interval_bridge_prefix_mean T r t hT hr.le hrT t.property.1 t.property.2,
      actualIntervalBridge_mean r t hr t.property.1 t.property.2]
  · intro s t
    simp only [Function.comp_def, Sum.elim_inl]
    rw [interval_bridge_prefix_covariance T r s t hT hr hrT
      s.property.1 s.property.2 t.property.1 t.property.2,
      actualIntervalBridge_covariance r s t hr s.property.1 s.property.2 t.property.1 t.property.2]

end SRWTightness
