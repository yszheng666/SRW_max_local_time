import SRWTightness.SourceEarlyOrderedConditions
import SRWTightness.SourceCommonRootGeometry
import SRWTightness.RootOuterDomainGeometry

open Filter

namespace SRWTightness

/-- The early observation set lies in the common entrance domain,
and the root fits the outer disk. -/
theorem source_early_ordered_root_geometry :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let j := a - sourceEarlyDistanceGap a J₀
      let m := sourceCommonPairInnerRadius t j
      16 ≤ m ∧ sourceCommonPairObservation b w ⊆ sourceEntranceDomain m 1 (j + 1) b j ∧
        sourceExitDomain m 1 (j + 1) b 0 ⊆ diskFinset (Real.exp t) := by
  obtain ⟨Jmin, hh⟩ := source_early_ordered_conditions 0 0 0 0 (by norm_num) (by norm_num)
  refine ⟨Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hh⟩ := hh J₀ hJ₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [hh, source_common_root_annular_geometry] with t ht hg
  intro b w hbw ha hrange hlo hhi
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let j := a - sourceEarlyDistanceGap a J₀
  let m := sourceCommonPairInnerRadius t j
  obtain ⟨hm, _, _, _, hR, hsep, _, _⟩ := ht b w hbw ha hrange
  change 112 ≤ m at hm
  change 2 * (2 * Real.sqrt (normSq (w - b))) < m - 14 - 2 at hsep
  have hbuf : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  refine ⟨by linarith, ?_, ?_⟩
  · have hh : sourceCommonPairObservation b w ⊆ translateFinset b (diskFinset (m - 14)) :=
      Finset.image_subset_image (diskFinset_mono _ _ (by positivity) (by linarith))
    simpa only [sourceEntranceDomain, sourceRecordRadius, Nat.cast_add, Nat.cast_one,
      sub_self, Real.exp_zero, mul_one, hbuf] using hh
  · have hroot := (hg b j hlo hhi).2
    have he := source_tree_exit_growing m 1 (j + 1) b j (by omega)
    simp only [sourceTreeExit, Nat.sub_self, hbuf] at he
    rw [he, growingRecordExit]
    have hrad : 0 < growingRecordRadius m j := (sourceCommonPairInnerRadius_pos t j).trans_le
      (growingRecordRadius_ge_base m (sourceCommonPairInnerRadius_pos t j).le j)
    exact (root_domain_and_exit_inside b _ (Real.exp t) (by positivity) hroot).1

end SRWTightness
