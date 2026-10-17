import SRWTightness.IntervalBridgeSuffixCovariance
import SRWTightness.GaussianProcessLawUniqueness
import SRWTightness.ExternalBridgeReflection

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The future centered bridge segment is independent of the entire earlier bridge path. -/
theorem interval_bridge_suffix_independent (T r : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r < T) :
    IndepFun (fun ω (t : Set.Icc (0 : ℝ) r) ↦ actualIntervalBridge T t ω)
      (fun ω (u : Set.Icc (0 : ℝ) (T - r)) ↦ intervalBridgeSuffixResidual T r u ω)
      gaussianCoefficientLaw := by
  exact IsGaussianProcess.indepFun_of_covariance_eq_zero
    (interval_bridge_past_suffix_gaussian T r hT hr hrT.le)
    (fun t ↦ (actualIntervalBridge_measurable T t).aemeasurable)
    (fun u ↦ (intervalBridgeSuffixResidual_measurable T r u).aemeasurable)
    (fun t u ↦ interval_bridge_suffix_past_covariance T r t u hT hr hrT
      t.property.1 t.property.2 u.property.1 u.property.2)

/-- The full future residual path is a centered bridge of the remaining duration. -/
theorem interval_bridge_suffix_path_law (T r : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r < T) :
    gaussianCoefficientLaw.map (fun ω (u : Set.Icc (0 : ℝ) (T - r)) ↦
      intervalBridgeSuffixResidual T r u ω) =
    gaussianCoefficientLaw.map (fun ω (u : Set.Icc (0 : ℝ) (T - r)) ↦
      actualIntervalBridge (T - r) u ω) := by
  apply gaussian_process_law_eq_of_mean_covariance gaussianCoefficientLaw _ _
    ((interval_bridge_past_suffix_gaussian T r hT hr hrT.le).comp_right Sum.inr)
    (actualIntervalBridge_gaussian (T - r) (sub_pos.mpr hrT))
  · exact measurable_pi_lambda _ (fun u ↦ intervalBridgeSuffixResidual_measurable T r u)
  · exact measurable_pi_lambda _ (fun u ↦ actualIntervalBridge_measurable (T - r) u)
  · intro u
    simp only [Function.comp_def, Sum.elim_inr]
    rw [interval_bridge_suffix_mean T r u hT hr hrT.le u.property.1 u.property.2,
      actualIntervalBridge_mean (T - r) u (sub_pos.mpr hrT) u.property.1 u.property.2]
  · intro u v
    simp only [Function.comp_def, Sum.elim_inr]
    rw [interval_bridge_suffix_covariance T r u v hT hr hrT
      u.property.1 u.property.2 v.property.1 v.property.2,
      actualIntervalBridge_covariance (T - r) u v (sub_pos.mpr hrT)
        u.property.1 u.property.2 v.property.1 v.property.2]

/-- A prescribed endpoint does not alter independence of the future residual from the past. -/
theorem endpoint_bridge_suffix_independent (T b r : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r < T) :
    IndepFun (fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω)
      (fun ω (u : Set.Icc (0 : ℝ) (T - r)) ↦ intervalBridgeSuffixResidual T r u ω)
      gaussianCoefficientLaw := by
  let H : (Set.Icc (0 : ℝ) r → ℝ) → (Set.Icc (0 : ℝ) r → ℝ) :=
    fun p t ↦ p t + (t : ℝ) / T * b
  have hH : Measurable H := by dsimp [H]; fun_prop
  exact (interval_bridge_suffix_independent T r hT hr hrT).comp hH measurable_id

/-- The future endpoint bridge reconstructs exactly from its intermediate value and residual. -/
theorem endpoint_bridge_suffix_reconstruction (T b r u : ℝ)
    (hT : 0 < T) (hrT : r < T) (ω : GaussianCoefficientSpace) :
    endpointBrownianBridge T b (r + u) ω = intervalBridgeSuffixResidual T r u ω +
      (1 - u / (T - r)) * endpointBrownianBridge T b r ω + u / (T - r) * b := by
  have hTr : 0 < T - r := sub_pos.mpr hrT
  unfold endpointBrownianBridge intervalBridgeSuffixResidual
  field_simp
  <;> ring

end SRWTightness
