import SRWTightness.SiteChildRangeScan
import SRWTightness.VisitTraceRange
import SRWTightness.ExternalTraceReconstruction
import SRWTightness.ChildIntervalOrder

namespace SRWTightness

/-- The site scanner on a finite word gives exactly the original complete child intervals. -/
theorem word_child_site_segments (K C : Finset Site) (x : Site) (w : PathWord) :
    scanSiteChildren K C none (siteRange x (wordPath w) 0 (w.length + 1)) =
      (wordChildIntervals K C x w).map
        (fun q ↦ siteRange x (wordPath w) q.1 (q.2 + 1 - q.1)) := by
  simpa [wordChildIntervals, List.range_eq_range'] using
    scan_site_children_range K C x (wordPath w) 0 (w.length + 1) none x
      (by intro a he; cases he)

/-- Decoding complete site segments recovers both entrance sites and every original direction. -/
theorem word_child_site_decode (K C : Finset Site) (x : Site) (w : PathWord) :
    (scanSiteChildren K C none (siteRange x (wordPath w) 0 (w.length + 1))).map
      (fun zs ↦ (zs.headD x, siteListWord zs)) =
      wordChildRecords K C x (fun y u ↦ (y, u)) w := by
  rw [word_child_site_segments, List.map_map]
  unfold wordChildRecords
  apply List.map_congr_left
  intro q hq
  have hlt : q.1 < q.2 :=
    scanChildIntervals_start_lt_end K C x (wordPath w) _ List.pairwise_lt_range none
      (by intro a he; cases he) q hq
  have hlen : q.2 + 1 - q.1 = (q.2 - q.1) + 1 := by omega
  dsimp only [Function.comp_def]
  rw [hlen, site_list_word_range, site_range_cons]
  rfl

/-- Filtering all sites, including an unobserved endpoint, gives the original trace. -/
theorem word_site_range_filter_eq_trace (E : Finset Site) (x : Site) (w : PathWord)
    (hout : x + position (wordPath w) w.length ∉ E) :
    (siteRange x (wordPath w) 0 (w.length + 1)).filter (fun z ↦ z ∈ E) =
      wordVisitTrace E x w := by
  rw [site_range_snoc, List.filter_append]
  simp only [Nat.zero_add]
  have he : List.filter (fun z ↦ decide (z ∈ E))
      [x + position (wordPath w) w.length] = [] := by simp [hout]
  rw [he, List.append_nil, word_visit_trace_eq_range]
  simp [siteRange, visitTraceRange, List.range_eq_range']

/-- The original finite-word reconstruction interface is internally supplied by the site scanner. -/
theorem trace_excursion_reconstruction_input_internal : TraceExcursionReconstructionInput := by
  intro K C E x hKC hCE hboundary
  refine ⟨fun ξ ↦ (scanSiteChildren K C none ξ).map
    (fun zs ↦ (zs.headD x, siteListWord zs)), ?_⟩
  intro w hout
  change (scanSiteChildren K C none (wordVisitTrace E x w)).map
    (fun zs ↦ (zs.headD x, siteListWord zs)) = _
  rw [← word_site_range_filter_eq_trace E x w hout,
    scan_site_children_filter K C E hKC hCE hboundary _ none
      (site_range_is_chain x (wordPath w) 0 (w.length + 1))
      (by intro p acc he; cases he)]
  exact word_child_site_decode K C x w

end SRWTightness
