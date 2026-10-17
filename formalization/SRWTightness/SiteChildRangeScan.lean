import SRWTightness.SiteChildTraceScan
import SRWTightness.SiteRange
import SRWTightness.ChildIntervalExtraction

namespace SRWTightness

/-- Scanning actual sites recovers the exact site segments of the original interval scanner. -/
theorem scan_site_children_range (K C : Finset Site) (x : Site) (ω : Sample)
    (i n : ℕ) (s : Option ℕ) (p : Site) (hs : ∀ a, s = some a → a < i) :
    scanSiteChildren K C (s.map (fun a ↦ (p, siteRange x ω a (i - a))))
      (siteRange x ω i n) =
      (scanChildIntervals K C x ω s (List.range' i n)).map
        (fun q ↦ siteRange x ω q.1 (q.2 + 1 - q.1)) := by
  induction n generalizing i s p with
  | zero => simp [siteRange, scanSiteChildren, scanChildIntervals]
  | succ n ih =>
    have hn : ∀ a, (none : Option ℕ) = some a → a < i + 1 := by
      intro a h
      cases h
    rw [site_range_cons, List.range'_succ]
    cases s with
    | none =>
      simp only [Option.map_none, scanSiteChildren, scanChildIntervals]
      by_cases hz : x + position ω i ∈ K
      · rw [if_pos hz, if_pos hz]
        have hh := ih (i + 1) (some i) (x + position ω i)
          (by intro a he; cases he; omega)
        simpa [siteRange] using hh
      · rw [if_neg hz, if_neg hz]
        exact ih (i + 1) none p hn
    | some a =>
      have ha : a < i := hs a rfl
      have he : siteRange x ω a (i - a) ++ [x + position ω i] =
          siteRange x ω a (i + 1 - a) := by
        have hlen : i + 1 - a = (i - a) + 1 := by omega
        rw [hlen, site_range_snoc, Nat.add_sub_of_le ha.le]
      simp only [Option.map_some, scanSiteChildren, scanChildIntervals]
      by_cases hz : x + position ω i ∈ C
      · rw [if_neg (not_not.mpr hz), if_neg (not_not.mpr hz), he]
        exact ih (i + 1) (some a) (x + position ω i)
          (by intro b hb; cases hb; omega)
      · rw [if_pos hz, if_pos hz, List.map_cons, he]
        congr 1
        exact ih (i + 1) none p hn

end SRWTightness
