import SRWTightness.SourceKilledEntranceCount
import SRWTightness.SourceForwardDirectCount
import SRWTightness.WordChildCountMonotone

open MeasureTheory

namespace SRWTightness

/-- Later exit balls are contained in earlier exit balls at the same source scales. -/
theorem sourceExitDomain_subset_of_index_le (m r : ℝ) (ℓ : ℕ) (b : Site) (k i : ℕ)
    (hr : 0 ≤ r) (hm : 0 ≤ m) (hki : k ≤ i) :
    sourceExitDomain m r ℓ b i ⊆ sourceExitDomain m r ℓ b k := by
  unfold sourceExitDomain
  apply Finset.image_subset_image
  apply diskFinset_mono
  · unfold sourceRecordRadius sourceRecordBuffer
    positivity
  · have hmono := sourceRecordRadius_antitone m hm ℓ hki
    linarith

/-- Forward forest counts are bounded by all point-shell entrances before killed exit. -/
theorem source_forward_count_le_point_entrances (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ k i : ℕ) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hki : k ≤ i) (hi : i + 1 ≤ ℓ) (b : Site) (D : Finset Site)
    (hCD : sourceExitDomain m r ℓ b k ⊆ D) (K C : Finset Site)
    (hK : sourceEntranceDomain m r ℓ b i ⊆ K) (hKC : K ⊆ C)
    (hC : C ⊆ sourceExitDomain m r ℓ b i) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    sourceForwardRecordCount m r ℓ k i b D x ω ≤
      (killedChildEntranceTimes D K C x ω).length := by
  have hm0 : 0 ≤ m := by unfold sourceRecordBuffer at hm; linarith
  have hCP : C ⊆ D := hC.trans
    ((sourceExitDomain_subset_of_index_le m r ℓ b k i hr hm0 hki).trans hCD)
  rw [source_forward_count_eq_direct hF m r ℓ k i hr hm hki hi b D hCD x ω hfin]
  calc
    _ ≤ (killedChildIntervals D K C x ω).length :=
      killedChildIntervals_length_mono D _ _ K C hK hKC hC x ω
    _ = _ := killedChildIntervals_length_eq_entrances D K C hKC hCP x ω hfin

/-- The same forward-versus-entrance comparison holds almost surely for the original killed walk. -/
theorem source_forward_count_le_point_entrances_ae (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ k i : ℕ) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hki : k ≤ i) (hi : i + 1 ≤ ℓ) (b : Site) (D : Finset Site)
    (hCD : sourceExitDomain m r ℓ b k ⊆ D) (K C : Finset Site)
    (hK : sourceEntranceDomain m r ℓ b i ⊆ K) (hKC : K ⊆ C)
    (hC : C ⊆ sourceExitDomain m r ℓ b i) (x : Site) :
    ∀ᵐ ω ∂pathLaw, sourceForwardRecordCount m r ℓ k i b D x ω ≤
      (killedChildEntranceTimes D K C x ω).length := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  exact source_forward_count_le_point_entrances hF m r ℓ k i hr hm hki hi b D
    hCD K C hK hKC hC x ω hfin

end SRWTightness
