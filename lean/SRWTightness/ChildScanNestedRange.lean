import SRWTightness.ChildScanNestedBlock
import SRWTightness.ChildRangeRenewal

namespace SRWTightness

/-- At a parent entrance and exit, the nested full-time scan splits into block and remainder. -/
theorem scanChildIntervals_nested_range (K C K' C' : Finset Site)
    (hKC' : K' ⊆ C') (hK : K' ⊆ K) (hC : C' ⊆ C)
    (x : Site) (ω : Sample) (a b N : ℕ) (hab : a < b) (hb : b ≤ N)
    (hpre : ∀ i < a, x + position ω i ∉ K)
    (hout : x + position ω b ∉ C) :
    scanChildIntervals K' C' x ω none (List.range (N + 1)) =
      scanChildIntervals K' C' x ω none
        (a :: (List.range' (a + 1) (b - a - 1) ++ [b])) ++
      scanChildIntervals K' C' x ω none (List.range' (b + 1) (N - b)) := by
  rw [child_time_range_split a b N hab hb]
  have hh := scanChildIntervals_nested_block K C K' C' hKC' hK hC x ω
    (List.range a) (a :: List.range' (a + 1) (b - a - 1))
    (List.range' (b + 1) (N - b)) b
    (fun i hi ↦ hpre i (List.mem_range.mp hi)) hout
  simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using hh

end SRWTightness
