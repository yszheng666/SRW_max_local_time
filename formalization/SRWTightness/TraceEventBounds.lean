import SRWTightness.TraceAtomBounds
import SRWTightness.CountableRecordRelativeEvents

open MeasureTheory
namespace SRWTightness

/-- Uniform trace-atom comparison extends to every event determined by the complete trace. -/
theorem trace_event_bounds (D K : Finset Site) (x e : Site) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (he : 0 < traceExitProbability D x e)
    (hratio : ∀ ξ : List Site,
      0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ} →
      |(pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
        traceExitProbability D x e) / pathLaw.real {ω | killedVisitTrace D K x ω = ξ} - 1| ≤ ε)
    (s : Set (List Site)) :
    ((1 - ε) * traceExitProbability D x e) * pathLaw.real {ω | killedVisitTrace D K x ω ∈ s} ≤
      pathLaw.real {ω | killedVisitTrace D K x ω ∈ s ∧ domainExitLocation D x ω = e} ∧
    pathLaw.real {ω | killedVisitTrace D K x ω ∈ s ∧ domainExitLocation D x ω = e} ≤
      ((1 + ε) * traceExitProbability D x e) * pathLaw.real {ω | killedVisitTrace D K x ω ∈ s} := by
  have hf (r : List Site) : MeasurableSet ((killedVisitTrace D K x) ⁻¹' {r}) :=
    (measurable_killedPathWord D x) (Set.to_countable {w : PathWord | wordVisitTrace K x w = r}).measurableSet
  have hs : MeasurableSet ((killedVisitTrace D K x) ⁻¹' s) :=
    (measurable_killedPathWord D x) (Set.to_countable {w : PathWord | wordVisitTrace K x w ∈ s}).measurableSet
  have hh := countable_record_relative_events
    (pathLaw.restrict {ω | domainExitLocation D x ω = e}) pathLaw
    (killedVisitTrace D K x) (killedVisitTrace D K x)
    ((1 - ε) * traceExitProbability D x e) ((1 + ε) * traceExitProbability D x e)
    (mul_nonneg (sub_nonneg.mpr hε1) he.le) (mul_nonneg (by linarith) he.le)
    hf hf (fun r ↦ ?_) s
  · rw [measureReal_restrict_apply hs] at hh
    exact hh
  · rw [measureReal_restrict_apply (hf r)]
    exact trace_atom_bounds D K x e ε he hratio r

end SRWTightness
