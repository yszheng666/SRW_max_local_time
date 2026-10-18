import SRWTightness.ExternalWordFlattening
import SRWTightness.SourcePrefixLevelGeometry

namespace SRWTightness

/-- Any later source exit domain is contained in an earlier one. -/
theorem sourceExitDomain_antitone (m r : ℝ) (ℓ : ℕ) (b : Site)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) :
    Antitone (sourceExitDomain m r ℓ b) :=
  antitone_nat_of_succ_le (fun j ↦ sourceExitDomain_successor_subset m r ℓ b j hr hm)

/-- The manuscript recursive extraction equals direct extraction at its last level, as an ordered
list of actual entrance/word pairs, when the parent word has completed its outer excursion. -/
theorem source_nested_word_flatten (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ : ℕ) (b : Site) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (k n : ℕ) (hn : k + n + 1 ≤ ℓ) (x : Site) (w : PathWord)
    (hend : x + position (wordPath w) w.length ∉ sourceExitDomain m r ℓ b k) :
    terminalWordRecords (sourceExcursionLevels m r ℓ b k (n + 1)) x w =
      wordChildRecords (sourceEntranceDomain m r ℓ b (k + n))
        (sourceExitDomain m r ℓ b (k + n)) x (fun y u ↦ (y, u)) w := by
  induction n generalizing k x w with
  | zero => simp [sourceExcursionLevels, terminalWordRecords, wordChildRecords, ← List.map_eq_flatMap]
  | succ n ih =>
    let K := sourceEntranceDomain m r ℓ b k
    let C := sourceExitDomain m r ℓ b k
    let K' := sourceEntranceDomain m r ℓ b (k + (n + 1))
    let C' := sourceExitDomain m r ℓ b (k + (n + 1))
    have hKC : K ⊆ C := sourceEntranceDomain_subset_exit m r ℓ b k hr hm (by omega)
    have hKC' : K' ⊆ C' := sourceEntranceDomain_subset_exit m r ℓ b _ hr hm hn
    have hK : K' ⊆ K := sourceEntranceDomain_subset_earlier m r ℓ b k _ hr hm hn (by omega)
    have hC : C' ⊆ C := sourceExitDomain_antitone m r ℓ b hr hm (by omega)
    calc
      _ = (wordChildRecords K C x
          (fun y u ↦ wordChildRecords K' C' y (fun z v ↦ (z, v)) u) w).flatten := by
        change ((wordChildIntervals K C x w).flatMap (fun q ↦
          terminalWordRecords (sourceExcursionLevels m r ℓ b (k + 1) (n + 1))
            (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2))) = _
        simp only [List.flatMap_def, wordChildRecords]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro q hq
        have hout := wordChildIntervals_slice_endpoint K C x w q hq
        have hout' : (x + position (wordPath w) q.1) +
            position (wordPath (slicePathWord w q.1 q.2)) (q.2 - q.1) ∉
              sourceExitDomain m r ℓ b (k + 1) :=
          fun h ↦ hout (sourceExitDomain_successor_subset m r ℓ b k hr hm h)
        have hh := ih (k + 1) (by omega) _ _ hout'
        simpa only [show k + 1 + n = k + (n + 1) by omega, wordChildRecords, K', C'] using hh
      _ = _ := hF K C K' C' hKC hKC' hK hC x w hend

end SRWTightness
