import SRWTightness.IntervalBridgeSuffixLaw
import SRWTightness.BridgeFutureFlatPathEvent
import SRWTightness.IndependentPastEventProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Future endpoint-bridge survival factors over any past event below the barrier. -/
theorem endpoint_bridge_future_survival (hReflection : BridgeReflectionInput)
    (T b q r : ℝ) (hT : 0 < T) (hr : 0 ≤ r) (hrT : r < T) (hbq : b < q)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (hpos : ∀ p ∈ A, p ⟨r, hr, le_rfl⟩ < q) :
    gaussianCoefficientLaw.real {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ A ∧
      ∀ u ∈ Set.Icc (0 : ℝ) (T - r), endpointBrownianBridge T b (r + u) ω ≤ q} =
    ∫ ω in (fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω) ⁻¹' A,
      1 - Real.exp (-(2 * (q - endpointBrownianBridge T b r ω) * (q - b) / (T - r)))
        ∂gaussianCoefficientLaw := by
  let μ := gaussianCoefficientLaw
  let P := fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω
  let Y := fun ω (u : Set.Icc (0 : ℝ) (T - r)) ↦ intervalBridgeSuffixResidual T r u ω
  let Z := fun ω (u : Set.Icc (0 : ℝ) (T - r)) ↦ actualIntervalBridge (T - r) u ω
  let ν := μ.map Z
  have hTr : 0 < T - r := sub_pos.mpr hrT
  have hP : Measurable P := measurable_pi_lambda _ (fun t ↦
    (actualIntervalBridge_measurable T t).add measurable_const)
  have hY : Measurable Y := measurable_pi_lambda _ (fun u ↦
    intervalBridgeSuffixResidual_measurable T r u)
  have hZ : Measurable Z := measurable_pi_lambda _ (fun u ↦
    actualIntervalBridge_measurable (T - r) u)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hZ.aemeasurable
  let E : Set ((Set.Icc (0 : ℝ) r → ℝ) × (Set.Icc (0 : ℝ) (T - r) → ℝ)) :=
    (fun p ↦ (p.1 ⟨r, hr, le_rfl⟩, p.2)) ⁻¹' bridgeFutureFlatPathEvent (T - r) b q
  have hE : MeasurableSet E :=
    (bridgeFutureFlatPathEvent_measurable (T - r) b q).preimage
      (((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd)
  have hl : HasLaw Y ν μ := ⟨hY.aemeasurable, interval_bridge_suffix_path_law T r hT hr hrT⟩
  have he := independent_past_event_probability μ ν P Y hP hY hl
    (endpoint_bridge_suffix_independent T b r hT hr hrT) A hA E hE
  have hright : (∫ ω in P ⁻¹' A, ν.real (Prod.mk (P ω) ⁻¹' E) ∂μ) =
      ∫ ω in P ⁻¹' A,
        1 - Real.exp (-(2 * (q - endpointBrownianBridge T b r ω) * (q - b) / (T - r))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (hA.preimage hP)] with ω hω
    exact bridge_future_flat_path_section hReflection (T - r) b q
      (endpointBrownianBridge T b r ω) hTr (hpos (P ω) hω) hbq
  rw [← hright, ← he]
  apply measureReal_congr
  filter_upwards [actualIntervalBridge_continuous T] with ω hω
  apply propext
  change (P ω ∈ A ∧ _) ↔ (P ω ∈ A ∧ _)
  apply and_congr_right
  intro hAω
  let f : ℝ → ℝ := fun u ↦ intervalBridgeSuffixResidual T r u ω +
    u / (T - r) * (b - endpointBrownianBridge T b r ω)
  have hsuf : Continuous (fun u ↦ intervalBridgeSuffixResidual T r u ω) := by
    unfold intervalBridgeSuffixResidual
    fun_prop
  have hf : Continuous f := hsuf.add ((continuous_id.div_const (T - r)).mul continuous_const)
  have hrec (u : ℝ) : endpointBrownianBridge T b (r + u) ω =
      f u + endpointBrownianBridge T b r ω := by
    rw [endpoint_bridge_suffix_reconstruction T b r u hT hrT]
    dsimp [f]
    ring
  have hevent : (∀ u ∈ Set.Icc (0 : ℝ) (T - r), endpointBrownianBridge T b (r + u) ω ≤ q) ↔
      ∀ u ∈ Set.Icc (0 : ℝ) (T - r), f u ≤ q - endpointBrownianBridge T b r ω := by
    simp_rw [hrec]
    constructor <;> intro h u hu <;> have hh := h u hu <;> linarith
  rw [hevent]
  have hc := continuous_flat_iff_dyadic f hf (T - r) (q - endpointBrownianBridge T b r ω)
  simpa only [dyadicFlatPathEvent, Set.mem_setOf_eq, bridgeFutureFlatPathEvent,
    Set.mem_preimage, E, P, Y, f] using hc

end SRWTightness
