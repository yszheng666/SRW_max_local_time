import SRWTightness.NestedSiteCounterErasure
import SRWTightness.SiteObservationRangeSplit

namespace SRWTightness

/-- Delete an internal time interval while retaining its entrance and its exit observations. -/
theorem nestedSiteCounterRun_erase_range (levels : List (Finset Site × Finset Site))
    (state : NestedSiteCounter) (x : Site) (ω : Sample) (p a b N : ℕ)
    (hp : p ≤ a) (hab : a < b) (hb : b ≤ N)
    (hlen : state.length = levels.length)
    (hin : ∀ i, a ≤ i → i < b → ∀ L ∈ levels,
      x + position ω i ∈ L.1 ∧ x + position ω i ∈ L.2) :
    nestedSiteCounterRun levels state (siteObservationRange x ω p (N - p + 1)) =
      nestedSiteCounterRun levels state
        (siteObservationRange x ω p (a - p + 1) ++
          siteObservationRange x ω b (N - b + 1)) := by
  have hpN : p ≤ N := by omega
  have hpn : N - p + 1 = (N + 1) - p := by omega
  have hbn : N - b + 1 = (N + 1) - b := by omega
  have hpa : a - p + 1 = a + 1 - p := by omega
  rw [hpn, hbn, hpa, siteObservationRange_split x ω p a (N + 1) hp (by omega),
    siteObservationRange_split x ω a b (N + 1) hab.le (by omega),
    siteObservationRange_cons x ω a b hab,
    ← siteObservationRange_snoc x ω p a hp]
  simp only [List.cons_append, List.append_assoc, List.singleton_append]
  apply nestedSiteCounterRun_erase_block levels state _ _ _ _ hlen
  · exact hin a le_rfl hab
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    have ht := List.mem_range'.mp hi
    exact hin i (by omega) (by omega)

end SRWTightness
