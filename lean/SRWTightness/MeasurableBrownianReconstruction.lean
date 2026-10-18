import SRWTightness.GaussianCrossSpaceLawUniqueness
import SRWTightness.EndpointProductBridgeProcess

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- An explicitly measurable Brownian-covariance path has the exact endpoint/bridge joint law. -/
theorem measurable_brownian_endpoint_bridge_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℝ → Ω → ℝ) (T : ℝ) (hT : 0 < T)
    (hX : IsGaussianProcess (fun t : Set.Icc (0 : ℝ) T ↦ X t) μ)
    (hXm : ∀ t : Set.Icc (0 : ℝ) T, Measurable (X t))
    (hm : ∀ t : Set.Icc (0 : ℝ) T, (∫ ω, X t ω ∂μ) = 0)
    (hc : ∀ s t : Set.Icc (0 : ℝ) T, cov[X s, X t; μ] = min (s : ℝ) t) :
    μ.map (fun ω ↦ (X T ω, fun t : Set.Icc (0 : ℝ) T ↦ X t ω)) =
      ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).map
        (fun p ↦ (p.1, fun t : Set.Icc (0 : ℝ) T ↦ endpointBrownianBridge T p.1 t p.2)) := by
  have hx : Measurable (fun ω (t : Set.Icc (0 : ℝ) T) ↦ X t ω) :=
    measurable_pi_lambda _ hXm
  have hy : Measurable (fun p : ℝ × GaussianCoefficientSpace ↦
      fun t : Set.Icc (0 : ℝ) T ↦ endpointBrownianBridge T p.1 t p.2) := by
    apply measurable_pi_lambda
    intro t
    exact ((actualIntervalBridge_measurable T t).comp measurable_snd).add
      (measurable_const.mul measurable_fst)
  have hLaw := gaussian_cross_space_process_law_eq μ
    ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw) _ _ hX
    (endpoint_product_bridge_gaussian T hT) hx hy
    (fun t ↦ (hm t).trans (endpoint_product_bridge_mean T t hT t.property.1 t.property.2).symm)
    (fun s t ↦ (hc s t).trans (endpoint_product_bridge_covariance T s t hT
      s.property.1 s.property.2 t.property.1 t.property.2).symm)
  let e : Set.Icc (0 : ℝ) T := ⟨T, hT.le, le_rfl⟩
  let H : (Set.Icc (0 : ℝ) T → ℝ) → ℝ × (Set.Icc (0 : ℝ) T → ℝ) := fun f ↦ (f e, f)
  have hH : Measurable H := (measurable_pi_apply e).prodMk measurable_id
  have hh := congrArg (fun ν : Measure (Set.Icc (0 : ℝ) T → ℝ) ↦ ν.map H) hLaw
  rw [Measure.map_map hH hx, Measure.map_map hH hy] at hh
  simpa only [Function.comp_def, H, e, endpointBrownianBridge_terminal T _ hT] using hh

end SRWTightness
