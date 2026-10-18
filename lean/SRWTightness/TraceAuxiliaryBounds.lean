import SRWTightness.TraceEventBounds
import SRWTightness.AuxiliaryRelativeComparison

open MeasureTheory
namespace SRWTightness

/-- Removing a prescribed exit preserves uniform relative bounds for trace tests with independent auxiliaries. -/
theorem trace_auxiliary_conditional_event_bounds {Ξ : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace (List Site)]
    (D K : Finset Site) (x e : Site) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (he : 0 < traceExitProbability D x e)
    (hratio : ∀ ξ : List Site,
      0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ} →
      |(pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
        traceExitProbability D x e) / pathLaw.real {ω | killedVisitTrace D K x ω = ξ} - 1| ≤ ε)
    (s : Set (List Site × Ξ)) (hs : MeasurableSet s) :
    let event := {p : Sample × Ξ | (killedVisitTrace D K x p.1, p.2) ∈ s}
    let joint := ((pathLaw.restrict {ω | domainExitLocation D x ω = e}).prod ν).real event
    (1 - ε) * (pathLaw.prod ν).real event ≤ joint / traceExitProbability D x e ∧
      joint / traceExitProbability D x e ≤ (1 + ε) * (pathLaw.prod ν).real event := by
  dsimp only
  let event := {p : Sample × Ξ | (killedVisitTrace D K x p.1, p.2) ∈ s}
  have hm : Measurable (killedVisitTrace D K x) :=
    measurable_killed_word_record D x (wordVisitTrace K x)
  have hEvent : MeasurableSet event :=
    ((hm.comp measurable_fst).prodMk measurable_snd) hs
  have hh := auxiliary_relative_comparison
    (pathLaw.restrict {ω | domainExitLocation D x ω = e}) pathLaw ν
    ((1 - ε) * traceExitProbability D x e) ((1 + ε) * traceExitProbability D x e)
    event event hEvent hEvent (Filter.Eventually.of_forall fun y ↦ ?_)
  · constructor
    · apply (le_div_iff₀ he).mpr
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hh.1
    · apply (div_le_iff₀ he).mpr
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hh.2
  · rw [measureReal_restrict_apply (measurable_prodMk_right hEvent)]
    exact trace_event_bounds D K x e ε hε hε1 he hratio
      {r | (r, y) ∈ s}

end SRWTightness
