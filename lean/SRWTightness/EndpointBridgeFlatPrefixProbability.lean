import SRWTightness.EndpointBridgeFutureSurvival
import SRWTightness.BridgeStrictBarrierBoundary

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Full bridge survival with a prefix event equals its exact future survival weight. -/
theorem endpoint_bridge_flat_prefix_probability (hReflection : BridgeReflectionInput)
    (T b q r : ℝ) (hT : 0 < T) (hq : 0 < q) (hbq : b < q)
    (hr : 0 ≤ r) (hrT : r < T) (B : Set (Set.Icc (0 : ℝ) r → ℝ)) (hB : MeasurableSet B) :
    gaussianCoefficientLaw.real {ω | ω ∈ bridgeFlatEvent T b q ∧
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ B} =
    ∫ ω in {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ B ∧
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ dyadicFlatPathEvent r q ∧
      endpointBrownianBridge T b r ω < q},
      1 - Real.exp (-(2 * (q - endpointBrownianBridge T b r ω) * (q - b) / (T - r)))
        ∂gaussianCoefficientLaw := by
  let P := fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω
  let A : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | p ∈ B ∧ p ∈ dyadicFlatPathEvent r q ∧ p ⟨r, hr, le_rfl⟩ < q}
  have hA : MeasurableSet A := hB.inter ((dyadicFlatPathEvent_measurable r q).inter
    (measurableSet_lt (measurable_pi_apply _) measurable_const))
  have he := endpoint_bridge_future_survival hReflection T b q r hT hr hrT hbq A hA
    (fun p hp ↦ hp.2.2)
  change gaussianCoefficientLaw.real _ = ∫ ω in P ⁻¹' A, _ ∂gaussianCoefficientLaw
  rw [← he]
  apply measureReal_congr
  filter_upwards [actualIntervalBridge_continuous T,
    bridge_strict_barrier_boundary hReflection T b q hT hq hbq] with ω hω hstrict
  have hc : Continuous (fun t ↦ endpointBrownianBridge T b t ω) :=
    hω.add ((continuous_id.div_const T).mul continuous_const)
  apply propext
  change (ω ∈ bridgeFlatEvent T b q ∧ P ω ∈ B) ↔
    (P ω ∈ A ∧ ∀ u ∈ Set.Icc (0 : ℝ) (T - r), endpointBrownianBridge T b (r + u) ω ≤ q)
  constructor
  · rintro ⟨hflat, hBω⟩
    have hpast : ∀ t ∈ Set.Icc (0 : ℝ) r, endpointBrownianBridge T b t ω ≤ q :=
      fun t ht ↦ hflat t ⟨ht.1, ht.2.trans hrT.le⟩
    refine ⟨⟨hBω, (continuous_flat_iff_dyadic _ hc r q).mp hpast,
      (hstrict.mpr hflat) r ⟨hr, hrT.le⟩⟩, ?_⟩
    intro u hu
    exact hflat (r + u) ⟨add_nonneg hr hu.1, by linarith [hu.2]⟩
  · rintro ⟨hAω, hfuture⟩
    have hpast := (continuous_flat_iff_dyadic _ hc r q).mpr hAω.2.1
    refine ⟨?_, hAω.1⟩
    intro t ht
    by_cases htr : t ≤ r
    · exact hpast t ⟨ht.1, htr⟩
    · have hu : t - r ∈ Set.Icc (0 : ℝ) (T - r) :=
        ⟨by linarith, by linarith [ht.2]⟩
      have hh := hfuture (t - r) hu
      rw [show r + (t - r) = t by ring] at hh
      exact hh

end SRWTightness
