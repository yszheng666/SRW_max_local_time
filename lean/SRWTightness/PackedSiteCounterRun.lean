import SRWTightness.NestedSiteCounterRangeErasure
import SRWTightness.ExteriorSiteObservations

namespace SRWTightness

/-- Deleting any ordered family of common-interior intervals preserves the full scanner state. -/
theorem nestedSiteCounterRun_packed (levels : List (Finset Site × Finset Site))
    (state : NestedSiteCounter) (x : Site) (w : PathWord) (intervals : List (ℕ × ℕ))
    (previous : ℕ) (hlen : state.length = levels.length)
    (horder : intervals.Pairwise (fun q r ↦ q.2 < r.1))
    (hbound : ∀ q ∈ intervals, previous ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ w.length)
    (hin : ∀ q ∈ intervals, ∀ i, q.1 ≤ i → i < q.2 → ∀ L ∈ levels,
      x + position (wordPath w) i ∈ L.1 ∧ x + position (wordPath w) i ∈ L.2) :
    nestedSiteCounterRun levels state
      (siteObservationRange x (wordPath w) previous (w.length - previous + 1)) =
        nestedSiteCounterRun levels state (packedSiteObservations x w previous intervals) := by
  induction intervals generalizing previous state with
  | nil => rfl
  | cons q intervals ih =>
    obtain ⟨hbefore, horderTail⟩ := List.pairwise_cons.mp horder
    obtain ⟨hp, hab, hb⟩ := hbound q List.mem_cons_self
    rw [nestedSiteCounterRun_erase_range levels state x (wordPath w)
      previous q.1 q.2 w.length hp hab hb hlen (hin q List.mem_cons_self)]
    rw [packedSiteObservations, nestedSiteCounterRun_append, nestedSiteCounterRun_append]
    apply ih _ q.2 (nestedSiteCounterRun_length levels state _ hlen) horderTail
    · intro r hr
      obtain ⟨_, hrlt, hrN⟩ := hbound r (List.mem_cons_of_mem q hr)
      exact ⟨(hbefore r hr).le, hrlt, hrN⟩
    · intro r hr
      exact hin r (List.mem_cons_of_mem q hr)

end SRWTightness
