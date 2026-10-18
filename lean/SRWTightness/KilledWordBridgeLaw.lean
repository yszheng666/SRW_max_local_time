import SRWTightness.KilledWordBridge
import Mathlib.Probability.ConditionalProbability

open MeasureTheory
namespace SRWTightness

/-- The complete stopped-word law conditional on its prescribed exit. -/
noncomputable def killedWordBridgeLaw (C : Finset Site) (x e : Site) : Measure PathWord :=
  (ProbabilityTheory.cond pathLaw {ω | domainExitLocation C x ω = e}).map (killedPathWord C x)

/-- Positive exit probability normalizes the conditional stopped-word law. -/
theorem killedWordBridgeLaw_isProbabilityMeasure (C : Finset Site) (x e : Site)
    (he : 0 < traceExitProbability C x e) : IsProbabilityMeasure (killedWordBridgeLaw C x e) := by
  have hn : pathLaw {ω | domainExitLocation C x ω = e} ≠ 0 := by
    intro hz
    have hz' : traceExitProbability C x e = 0 := by
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr hz
    exact he.ne' hz'
  letI := ProbabilityTheory.cond_isProbabilityMeasure hn
  exact Measure.isProbabilityMeasure_map (measurable_killedPathWord C x).aemeasurable

/-- The named bridge mass is the singleton mass of the normalized stopped-word law. -/
theorem killedWordBridgeLaw_singleton (C : Finset Site) (x e : Site) (w : PathWord) :
    (killedWordBridgeLaw C x e).real {w} = killedWordBridgeProbability C x e w := by
  rw [killedWordBridgeLaw, map_measureReal_apply (measurable_killedPathWord C x)
    (measurableSet_singleton w)]
  unfold Measure.real
  rw [ProbabilityTheory.cond_apply
    (measurableSet_eq_fun (measurable_domainExitLocation C x) measurable_const),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (pathLaw.real {ω | domainExitLocation C x ω = e})⁻¹ *
    pathLaw.real {ω | domainExitLocation C x ω = e ∧ killedPathWord C x ω = w} = _
  rw [show {ω | domainExitLocation C x ω = e ∧ killedPathWord C x ω = w} =
    {ω | killedPathWord C x ω = w ∧ domainExitLocation C x ω = e} by ext; exact and_comm]
  exact (div_eq_inv_mul _ _).symm

/-- Every event of projected internal records retains the actual prescribed-exit conditional law. -/
theorem killedWordBridgeLaw_record {R : Type*} (C : Finset Site) (x e : Site)
    (f : PathWord → R) (r : R) :
    (killedWordBridgeLaw C x e).real {w | f w = r} =
      pathLaw.real {ω | f (killedPathWord C x ω) = r ∧ domainExitLocation C x ω = e} /
        traceExitProbability C x e := by
  rw [killedWordBridgeLaw, map_measureReal_apply (measurable_killedPathWord C x)
    (Set.to_countable _).measurableSet]
  unfold Measure.real
  rw [ProbabilityTheory.cond_apply
    (measurableSet_eq_fun (measurable_domainExitLocation C x) measurable_const),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (pathLaw.real {ω | domainExitLocation C x ω = e})⁻¹ *
    pathLaw.real {ω | domainExitLocation C x ω = e ∧ f (killedPathWord C x ω) = r} = _
  rw [show {ω | domainExitLocation C x ω = e ∧ f (killedPathWord C x ω) = r} =
    {ω | f (killedPathWord C x ω) = r ∧ domainExitLocation C x ω = e} by ext; exact and_comm]
  exact (div_eq_inv_mul _ _).symm

end SRWTightness
