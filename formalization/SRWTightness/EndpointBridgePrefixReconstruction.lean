import SRWTightness.IntervalBridgePrefixLaw
import SRWTightness.IntervalBridgeIntermediateLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The intermediate value and centered prefix have their exact independent product law. -/
theorem endpoint_bridge_prefix_product_law (T b r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T) :
    gaussianCoefficientLaw.map (fun ω ↦
      (endpointBrownianBridge T b r ω,
        fun t : Set.Icc (0 : ℝ) r ↦ intervalBridgePrefixResidual T r t ω)) =
    (gaussianReal (r / T * b) (r * (T - r) / T).toNNReal).prod
      (gaussianCoefficientLaw.map
        (fun ω (t : Set.Icc (0 : ℝ) r) ↦ actualIntervalBridge r t ω)) := by
  have hm : Measurable (endpointBrownianBridge T b r) :=
    (actualIntervalBridge_measurable T r).add measurable_const
  have hn : Measurable (fun ω (t : Set.Icc (0 : ℝ) r) ↦
      intervalBridgePrefixResidual T r t ω) :=
    measurable_pi_lambda _ (fun t ↦ intervalBridgePrefixResidual_measurable T r t)
  have hshift : Measurable (fun a : ℝ ↦ a + r / T * b) := measurable_id.add measurable_const
  have hi := (interval_bridge_prefix_independent T r hT hr hrT).comp measurable_id hshift
  have hind : IndepFun (endpointBrownianBridge T b r)
      (fun ω (t : Set.Icc (0 : ℝ) r) ↦ intervalBridgePrefixResidual T r t ω)
      gaussianCoefficientLaw := hi.symm
  rw [hind.map_prod_eq_prod_map_map hm.aemeasurable hn.aemeasurable,
    (endpoint_bridge_intermediate_law T b r hT hr.le hrT).map_eq,
    interval_bridge_prefix_path_law T r hT hr hrT]

/-- The whole prefix of an endpoint bridge reconstructs from its Gaussian middle
and shorter bridge. -/
theorem endpoint_bridge_prefix_reconstruction (T b r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T) :
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω) =
    ((gaussianReal (r / T * b) (r * (T - r) / T).toNNReal).prod
      (gaussianCoefficientLaw.map (fun ω (t : Set.Icc (0 : ℝ) r) ↦ actualIntervalBridge r t ω))).map
        (fun p (t : Set.Icc (0 : ℝ) r) ↦ p.2 t + (t : ℝ) / r * p.1) := by
  let H : (ℝ × (Set.Icc (0 : ℝ) r → ℝ)) → (Set.Icc (0 : ℝ) r → ℝ) :=
    fun p t ↦ p.2 t + (t : ℝ) / r * p.1
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hP : Measurable (fun ω ↦
      (endpointBrownianBridge T b r ω,
        fun t : Set.Icc (0 : ℝ) r ↦ intervalBridgePrefixResidual T r t ω)) :=
    ((actualIntervalBridge_measurable T r).add measurable_const).prodMk
      (measurable_pi_lambda _ (fun t ↦ intervalBridgePrefixResidual_measurable T r t))
  have he := congrArg (fun μ : Measure (ℝ × (Set.Icc (0 : ℝ) r → ℝ)) ↦ μ.map H)
    (endpoint_bridge_prefix_product_law T b r hT hr hrT)
  rw [Measure.map_map hH hP] at he
  rw [← he]
  congr 1
  funext ω t
  dsimp [H, Function.comp_def, endpointBrownianBridge, intervalBridgePrefixResidual]
  field_simp
  <;> ring

end SRWTightness
