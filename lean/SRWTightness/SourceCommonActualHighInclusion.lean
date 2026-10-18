import SRWTightness.SourceCommonActualVisits
import SRWTightness.SourceCommonReferenceHighEvent

namespace SRWTightness

/-- The common root list retains the original walk's level-zero count. -/
theorem source_common_actual_forest_length (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) :
    (sourceCommonActualForest t b K j ω).length = sourceActualCount t b 0 ω := by
  rw [source_common_actual_forest_eq]
  have hc : sourceActualCount t b 0 ω =
      sourceForwardRecordCount (sourceCommonPairInnerRadius t j) 1 (j + 1) 0 0 b
        (diskFinset (Real.exp t)) 0 ω := by
    rw [sourceCommonPairInnerRadius, sourceForwardRecordCount_rebase]
    rfl
  rw [hc, source_forward_root_count]
  simp only [killedChildRecords, wordChildRecords, List.length_map]

/-- Original counts and high local times imply the exact common reference-record event. -/
theorem source_common_actual_high_inclusion (t : ℝ) (b w : Site) (j : ℕ)
    (hpair : ({b, w} : Finset Site) ⊆ sourceCommonPairObservation b w)
    (ω : Sample) (hm : 16 ≤ sourceCommonPairInnerRadius t j)
    (hK : sourceCommonPairObservation b w ⊆
      translateFinset b (diskFinset (sourceCommonPairInnerRadius t j - 16)))
    (hroot : sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0 ⊆
      diskFinset (Real.exp t)) (hfin : domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤)
    (hone : sourceActualCount t b 0 ω = 1)
    (hbar : ∀ i : ℕ, 0 < i → i ≤ j →
      Real.sqrt (2 * (sourceActualCount t b i ω : ℝ)) ≤ sourceCommonPairEndpoint t i)
    (hhigh : ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2 ≤
      (domainLocalTime (diskFinset (Real.exp t)) 0 v ω : ℝ)) :
    ∃ r ∈ sourceCommonPrefixHighEvent t b w j hpair,
      sourceCommonActualForest t b (sourceCommonPairObservation b w) j ω = [r] := by
  have hlen := (source_common_actual_forest_length t b (sourceCommonPairObservation b w) j ω).trans hone
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨r, ⟨?_, ?_⟩, hr⟩
  · intro i hi hij
    unfold geometricGWHeight
    rw [source_common_actual_forest_population t b _ j ω r hr i hij]
    exact hbar i hi hij
  · intro v
    have hv := source_common_actual_mark_visits t b (sourceCommonPairObservation b w) j ω r hr
      hm hK hroot hfin ⟨v, hpair v.property⟩
    change (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2 ≤
      (sumMarks _ _ (terminalListSamples 0 _ (finiteRecordLeaves j r)) ⟨v, hpair v.property⟩ : ℝ)
    rw [hv]
    exact hhigh v

end SRWTightness
