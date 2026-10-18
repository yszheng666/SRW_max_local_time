import SRWTightness.BridgeConditionalProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Countable flat-barrier test on the restricted path space. -/
def dyadicFlatPathEvent (T q : ℝ) : Set (Set.Icc (0 : ℝ) T → ℝ) :=
  {f | ∀ n j : ℕ, ∀ h : (j : ℝ) / 2 ^ n ≤ T,
    f ⟨(j : ℝ) / 2 ^ n, by positivity, h⟩ ≤ q}

/-- The countable flat-barrier test is measurable. -/
theorem dyadicFlatPathEvent_measurable (T q : ℝ) :
    MeasurableSet (dyadicFlatPathEvent T q) := by
  simp only [dyadicFlatPathEvent, Set.setOf_forall]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun j ↦
    MeasurableSet.iInter fun h ↦ measurableSet_le (measurable_pi_apply _) measurable_const

/-- On continuous paths the countable test is the full closed-interval barrier event. -/
theorem continuous_flat_iff_dyadic (f : ℝ → ℝ) (hf : Continuous f) (T q : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, f t ≤ q) ↔
      (fun t : Set.Icc (0 : ℝ) T ↦ f t) ∈ dyadicFlatPathEvent T q := by
  simpa only [dyadicFlatPathEvent, Set.mem_setOf_eq, Set.mem_Icc, and_imp] using
    continuous_barrier_iff_dyadic f (fun _ ↦ q) hf continuous_const T

/-- The independent endpoint/bridge product event without an endpoint window. -/
def endpointFlatProductEvent (T q : ℝ) : Set (ℝ × GaussianCoefficientSpace) :=
  (fun p (t : Set.Icc (0 : ℝ) T) ↦ endpointBrownianBridge T p.1 t p.2) ⁻¹'
    dyadicFlatPathEvent T q

/-- The full endpoint/bridge product flat event is measurable. -/
theorem endpointFlatProductEvent_measurable (T q : ℝ) :
    MeasurableSet (endpointFlatProductEvent T q) := by
  apply (dyadicFlatPathEvent_measurable T q).preimage
  apply measurable_pi_lambda
  intro t
  exact ((actualIntervalBridge_measurable T t).comp measurable_snd).add
    (measurable_const.mul measurable_fst)

/-- Every endpoint section has the actual continuous flat-bridge probability. -/
theorem endpointFlatProductEvent_section (T q b : ℝ) :
    gaussianCoefficientLaw.real (Prod.mk b ⁻¹' endpointFlatProductEvent T q) =
      gaussianCoefficientLaw.real (bridgeFlatEvent T b q) := by
  apply measureReal_congr
  filter_upwards [actualIntervalBridge_continuous T] with ω hω
  apply propext
  exact (continuous_flat_iff_dyadic _
    (hω.add ((continuous_id.div_const T).mul continuous_const)) T q).symm

end SRWTightness
