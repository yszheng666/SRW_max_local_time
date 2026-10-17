import SRWTightness.BridgeStrictBarrierBoundary

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Conditioning the actual positive bridge on closed or strict survival gives the same law. -/
theorem positive_bridge_condition_strict (hReflection : BridgeReflectionInput)
    (T x y : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) :
    positiveBridgeCoefficientLaw T x y = ProbabilityTheory.cond gaussianCoefficientLaw
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < positiveEndpointBridge T x y t ω} := by
  have he : bridgeFlatEvent T (x - y) x =ᵐ[gaussianCoefficientLaw]
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < positiveEndpointBridge T x y t ω} := by
    filter_upwards [bridge_strict_barrier_boundary hReflection T (x - y) x hT hx
      (by linarith)] with ω hω
    apply propext
    change (ω ∈ bridgeFlatEvent T (x - y) x) ↔
      ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < positiveEndpointBridge T x y t ω
    simpa only [positiveEndpointBridge, sub_pos] using hω.symm
  unfold positiveBridgeCoefficientLaw ProbabilityTheory.cond
  rw [measure_congr he, Measure.restrict_congr_set he]

/-- Under its original conditioning, the actual positive bridge stays strictly positive. -/
theorem positive_bridge_strict_survival (hReflection : BridgeReflectionInput)
    (T x y : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) :
    ∀ᵐ ω ∂positiveBridgeCoefficientLaw T x y,
      ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < positiveEndpointBridge T x y t ω := by
  have hh := (cond_absolutelyContinuous (μ := gaussianCoefficientLaw)
    (s := bridgeFlatEvent T (x - y) x)).ae_le
    (bridge_strict_barrier_boundary hReflection T (x - y) x hT hx (by linarith))
  filter_upwards [hh, ae_cond_mem₀ (bridgeFlatEvent_nullMeasurable T (x - y) x)]
    with ω hω hm
  intro t ht
  exact sub_pos.mpr (hω.mpr hm t ht)

end SRWTightness
