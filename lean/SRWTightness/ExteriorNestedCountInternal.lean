import SRWTightness.ExternalExteriorCountInvariance
import SRWTightness.PackedSiteCounterRun
import SRWTightness.NestedSiteCounterCorrectness
import SRWTightness.NestedSiteCountWord
import SRWTightness.ChildIntervalSeparation
import SRWTightness.ChildIntervalInterior

namespace SRWTightness

/-- The actual exterior record determines every recursively extracted outer excursion count. -/
theorem terminalWordRecords_length_exterior (K C : Finset Site) (label : Site → Bool)
    (x : Site) (levels : List (Finset Site × Finset Site)) (hKC : K ⊆ C)
    (hlevels : ∀ L ∈ levels, L.1 ⊆ L.2 ∧ C ⊆ L.1) (w : PathWord) :
    (terminalWordRecords levels x w).length = nestedSiteCounterValue
      (nestedSiteCounterRun levels (nestedSiteCounterInitial levels)
        (exteriorSiteObservations x (wordExteriorRecord K C label x w))) := by
  have hrun := nestedSiteCounterRun_packed levels (nestedSiteCounterInitial levels) x w
    (wordChildIntervals K C x w) 0 (by simp [nestedSiteCounterInitial])
    (scanChildIntervals_separated K C x (wordPath w) _ List.pairwise_lt_range none)
    (by
      intro q hq
      have ht := wordChildIntervals_endpoint_le K C x w q hq
      have ho := scanChildIntervals_start_lt_end K C x (wordPath w) _
        List.pairwise_lt_range none (by intro a he; cases he) q hq
      exact ⟨Nat.zero_le _, ho, ht.2⟩)
    (by
      intro q hq i hai hib L hL
      have hc := wordChildIntervals_interior K C hKC x w q hq i hai hib
      have hl := (hlevels L hL).2 hc
      exact ⟨hl, (hlevels L hL).1 hl⟩)
  have hrec : exteriorSiteObservations x (wordExteriorRecord K C label x w) =
      packedSiteObservations x w 0 (wordChildIntervals K C x w) := by
    simpa only [position_zero_as_zero, add_zero, wordExteriorRecord] using
      exteriorSiteObservations_pack label x w (wordChildIntervals K C x w) 0
  rw [hrec]
  rw [← nestedSiteCount_word, ← nestedSiteCounter_correct, wordSiteObservations_eq_range]
  exact congrArg nestedSiteCounterValue (by simpa only [Nat.sub_zero] using hrun)

/-- The original deterministic exterior nested-count invariance input is internally proved. -/
theorem exteriorNestedCountInvarianceInput_internal : ExteriorNestedCountInvarianceInput := by
  intro K C label x levels hKC hlevels u v he
  have hl : ∀ L ∈ levels, L.1 ⊆ L.2 ∧ C ⊆ L.1 :=
    fun L hL ↦ ⟨(hlevels L hL).1, (hlevels L hL).2.1⟩
  rw [terminalWordRecords_length_exterior K C label x levels hKC hl u,
    terminalWordRecords_length_exterior K C label x levels hKC hl v, he]

end SRWTightness
