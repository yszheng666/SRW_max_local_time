import SRWTightness.WordFlatteningInternal
import SRWTightness.SourceNestedWordFlatten
import SRWTightness.SourceForwardRecordCounts
import SRWTightness.KilledWordFlatten

namespace SRWTightness

/-- The source forward count equals direct complete extraction at that level. -/
theorem source_forward_count_eq_direct_internal
    (m r : ℝ) (ℓ k i : ℕ) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hki : k ≤ i) (hi : i + 1 ≤ ℓ) (b : Site) (D : Finset Site)
    (hCD : sourceExitDomain m r ℓ b k ⊆ D) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    sourceForwardRecordCount m r ℓ k i b D x ω =
      (killedChildIntervals D (sourceEntranceDomain m r ℓ b i)
        (sourceExitDomain m r ℓ b i) x ω).length := by
  have hh := source_nested_word_flatten two_level_word_flattening_input_internal m r ℓ b hr hm k (i
    - k)
    (by omega) x (killedPathWord D x ω)
    (killedPathWord_endpoint_outside_child D _ hCD x ω hfin)
  have he : k + (i - k) = i := by omega
  rw [he] at hh
  unfold sourceForwardRecordCount actualTerminalWordRecords
  rw [hh]
  simp only [wordChildRecords, List.length_map]
  rfl

end SRWTightness
