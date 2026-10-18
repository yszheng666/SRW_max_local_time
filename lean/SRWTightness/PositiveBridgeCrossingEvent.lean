import SRWTightness.PositiveBridgeDomination
import SRWTightness.SourceBridgedEvent

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A measurable strict crossing test on the restricted path space. -/
def dyadicLowerPathEvent (s : ℝ) (bound : ℝ → ℝ) : Set (Set.Icc (0 : ℝ) s → ℝ) :=
  {f | ∃ n j : ℕ, ∃ h : (j : ℝ) / 2 ^ n ≤ s,
    f ⟨(j : ℝ) / 2 ^ n, by positivity, h⟩ < bound ((j : ℝ) / 2 ^ n)}

theorem dyadicLowerPathEvent_measurable (s : ℝ) (bound : ℝ → ℝ) :
    MeasurableSet (dyadicLowerPathEvent s bound) := by
  simp only [dyadicLowerPathEvent, Set.setOf_exists]
  exact MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun j ↦
    MeasurableSet.iUnion fun h ↦ measurableSet_lt (measurable_pi_apply _) measurable_const

theorem continuous_crossing_iff_dyadic (f bound : ℝ → ℝ) (hf : Continuous f)
    (hb : Continuous bound) (s : ℝ) :
    (∃ t ∈ Set.Icc (0 : ℝ) s, f t < bound t) ↔
      (fun t : Set.Icc (0 : ℝ) s ↦ f t) ∈ dyadicLowerPathEvent s bound := by
  constructor
  · rintro ⟨t, ht, hcross⟩
    by_contra hn
    have hle : ∀ n j : ℕ, (j : ℝ) / 2 ^ n ≤ s →
        bound ((j : ℝ) / 2 ^ n) ≤ f ((j : ℝ) / 2 ^ n) := by
      intro n j hj
      by_contra h
      exact hn ⟨n, j, hj, lt_of_not_ge h⟩
    exact (not_le_of_gt hcross)
      ((continuous_barrier_iff_dyadic bound f hb hf s).mpr hle t ht.1 ht.2)
  · rintro ⟨n, j, hj, hcross⟩
    exact ⟨(j : ℝ) / 2 ^ n, ⟨by positivity, hj⟩, hcross⟩

theorem positiveEndpointBridge_measurable (T x y t : ℝ) :
    Measurable (positiveEndpointBridge T x y t) := by
  unfold positiveEndpointBridge endpointBrownianBridge
  exact measurable_const.sub ((actualIntervalBridge_measurable T t).add measurable_const)

theorem positiveEndpointBridge_path_measurable (T x y s : ℝ) :
    Measurable (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y t ω) :=
  measurable_pi_iff.mpr (fun t ↦ positiveEndpointBridge_measurable T x y t)

theorem positiveEndpointBridge_ae_continuous (T x y : ℝ) :
    ∀ᵐ ω ∂positiveBridgeCoefficientLaw T x y,
      Continuous (fun t ↦ positiveEndpointBridge T x y t ω) := by
  apply (cond_absolutelyContinuous (μ := gaussianCoefficientLaw)
    (s := bridgeFlatEvent T (x - y) x)).ae_le
  filter_upwards [actualIntervalBridge_continuous T] with ω hω
  exact continuous_const.sub (hω.add ((continuous_id.div_const T).mul continuous_const))

/-- The measurable test and full-time crossing coincide under the actual conditioned bridge. -/
theorem positiveBridge_crossing_real (T x y s : ℝ) (bound : ℝ → ℝ)
    (hb : Continuous bound) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, positiveEndpointBridge T x y t ω < bound t} =
    ((positiveBridgeCoefficientLaw T x y).map
      (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y t ω)).real
      (dyadicLowerPathEvent s bound) := by
  rw [map_measureReal_apply (positiveEndpointBridge_path_measurable T x y s)
    (dyadicLowerPathEvent_measurable s bound)]
  apply measureReal_congr
  filter_upwards [positiveEndpointBridge_ae_continuous T x y] with ω hω
  exact propext (continuous_crossing_iff_dyadic _ bound hω hb s)

end SRWTightness
