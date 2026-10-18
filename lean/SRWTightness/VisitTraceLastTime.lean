import SRWTightness.VisitTraceRange

namespace SRWTightness

/-- Every nonempty finite chronological trace has a last visiting time. -/
theorem visit_trace_range_last_time (K : Finset Site) (x : Site) (ω : Sample)
    (N : ℕ) (h : visitTraceRange K x ω N ≠ []) :
    ∃ n < N, x + position ω n ∈ K ∧
      visitTraceRange K x ω N = visitTraceRange K x ω (n + 1) := by
  induction N with
  | zero => simp [visitTraceRange] at h
  | succ N ih =>
    by_cases hm : x + position ω N ∈ K
    · exact ⟨N, Nat.lt_succ_self N, hm, rfl⟩
    · have he : visitTraceRange K x ω (N + 1) = visitTraceRange K x ω N := by
        rw [visit_trace_range_succ, if_neg hm, List.append_nil]
      obtain ⟨n, hn, hmem, htrace⟩ := ih (he ▸ h)
      exact ⟨n, hn.trans (Nat.lt_succ_self N), hmem, he.trans htrace⟩

end SRWTightness
