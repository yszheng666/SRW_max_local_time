import SRWTightness.SourceCommonRootGeometry
import SRWTightness.SourceCommonPairObservationUniform
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.RootOuterDomainGeometry

open Filter
namespace SRWTightness

/-- All deterministic premises for common-prefix local-time recovery hold in the source annulus. -/
theorem source_common_actual_geometry :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      16 ≤ sourceCommonPairInnerRadius t j ∧
      sourceCommonPairObservation b w ⊆
        translateFinset b (diskFinset (sourceCommonPairInnerRadius t j - 16)) ∧
      sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0 ⊆
        diskFinset (Real.exp t) := by
  filter_upwards [source_common_root_annular_geometry, source_common_pair_observation_uniform,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hr ho ht
  intro b w j hbw hi hd hlo hhi
  have hm := ((sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1).trans
    (sourceCommonPairInnerRadius_ge_lower t j hd)
  have hobs := ho b w j hbw hi
  have hroot := (hr b j hlo hhi).2
  refine ⟨by linarith, ?_, ?_⟩
  · exact Finset.image_subset_image (diskFinset_mono _ _ (by positivity) (by linarith [hobs.2.1]))
  · have he := source_tree_exit_growing (sourceCommonPairInnerRadius t j) 1 (j + 1) b j (by omega)
    have hbuf : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
    simp only [sourceTreeExit, Nat.sub_self, hbuf] at he
    rw [he, growingRecordExit]
    have hrad : 0 < growingRecordRadius (sourceCommonPairInnerRadius t j) j :=
      (sourceCommonPairInnerRadius_pos t j).trans_le
        (growingRecordRadius_ge_base _ (sourceCommonPairInnerRadius_pos t j).le j)
    exact (root_domain_and_exit_inside b _ (Real.exp t) (by positivity) hroot).1

end SRWTightness
