import SRWTightness.ExternalKilledTraceFactorization

open MeasureTheory
namespace SRWTightness

/-- Every recorded visit belongs to the specified observation set. -/
theorem killed_visit_trace_mem (D K : Finset Site) (x : Site) (ω : Sample) (y : Site)
    (hy : y ∈ killedVisitTrace D K x ω) : y ∈ K := by
  classical
  unfold killedVisitTrace wordVisitTrace at hy
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hy).2

/-- Positive actual trace atoms have their final point in K; the default covers the empty list safely. -/
theorem killed_trace_last_mem (D K : Finset Site) (x : Site) (hx : x ∈ K) (ξ : List Site)
    (hξ : 0 < pathLaw.real {ω | killedVisitTrace D K x ω = ξ}) : ξ.getLastD x ∈ K := by
  have hn : ({ω | killedVisitTrace D K x ω = ξ} : Set Sample).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, measureReal_empty] at hξ
    linarith
  obtain ⟨ω, hω⟩ := hn
  change killedVisitTrace D K x ω = ξ at hω
  rw [← hω]
  rcases List.mem_cons.mp (List.getLastD_mem_cons (l := killedVisitTrace D K x ω) (a := x)) with h | h
  · simpa only [h] using hx
  · exact killed_visit_trace_mem D K x ω _ h

end SRWTightness
