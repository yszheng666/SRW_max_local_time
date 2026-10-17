import SRWTightness.SourceCommonOrderedRoots
import SRWTightness.SourceEarlyOrderedRootGeometry
import SRWTightness.SourceEarlyRootObservationGeometry
import SRWTightness.SourceCommonReferenceWord
import SRWTightness.SourceForwardDirectCount

open Filter

namespace SRWTightness

/-- Both original early short-root counts are exact sums over the selected common leaf marks. -/
theorem source_early_ordered_leaf_roots (hF : TwoLevelWordFlatteningInput) :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      (∀ z ∈ ({b, w} : Finset Site), Real.exp t / 4 ≤ Real.sqrt (normSq z) ∧
        Real.sqrt (normSq z) ≤ Real.exp t / 3) →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      ∀ (ω : Sample) (r : FiniteExcursionRecord WordMark j),
      domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ →
      sourceCommonOrderedForest t b (sourceCommonPairObservation b w) j ω = [r] →
      ∀ z ∈ ({b, w} : Finset Site),
      ((finiteRecordLeaves j r).map (sourceCommonWordRootCount t z ν)).sum =
        sourceActualCount t z ν ω := by
  obtain ⟨Jmin, hg⟩ := source_early_ordered_root_geometry
  refine ⟨Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨aG, haG, hg⟩ := hg J₀ hJ₀
  obtain ⟨aL, hl⟩ := source_early_distance_levels J₀
  refine ⟨aG + aL, by omega, ?_⟩
  filter_upwards [hg, hl, source_early_root_observation_geometry, source_early_level_bounds,
    source_common_root_annular_geometry,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ))]
    with t hg hl ho ht hroot hm16
  intro b w hbw ha hrange hann
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  have haG' : aG ≤ a := by change aG + aL ≤ a at ha; omega
  have haL : aL ≤ a := by change aG + aL ≤ a at ha; omega
  have hν : ν ≤ 2 * sourceCoarseLowerLevel t := (hl a haL hrange).2.2
  have hdepth : ν + 1 ≤ ℓ := (ht.2 ν hν).1
  have hb := hann b (by simp)
  obtain ⟨hm, hO, hD⟩ := hg b w hbw haG' hrange hb.1 hb.2
  have hshort := ho b w ν J hbw (haG.trans haG') hν rfl
  intro ω r hfin hr z hz
  obtain ⟨hLE, hEO, _⟩ := hshort z hz
  have hLO := hLE.trans hEO
  have hL := hLO.trans hO
  have hcommon : sourceEntranceDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b j ⊆
      sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b j :=
    sourceEntranceDomain_subset_exit _ 1 _ b j (by norm_num)
      (by norm_num [sourceRecordBuffer]; exact hm) (by omega)
  have hE := hEO.trans (hO.trans hcommon)
  have hsum := source_common_ordered_leaf_roots hF t b (sourceCommonPairObservation b w)
    (sourceEntranceDomain m 1 ℓ z ν) (sourceExitDomain m 1 ℓ z ν) j ω r hr
    hm hLE hLO hL hE hD hfin
  have hzann := hann z hz
  have hzfit := (hroot z j hzann.1 hzann.2).2
  have he := source_tree_exit_growing (sourceCommonPairInnerRadius t j) 1 (j + 1) z j
    (by omega)
  have hbuf : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  simp only [sourceTreeExit, Nat.sub_self, hbuf] at he
  have hrad : 0 < growingRecordRadius (sourceCommonPairInnerRadius t j) j :=
    (sourceCommonPairInnerRadius_pos t j).trans_le
      (growingRecordRadius_ge_base _ (sourceCommonPairInnerRadius_pos t j).le j)
  have hzD : sourceExitDomain m 1 ℓ z 0 ⊆ diskFinset (Real.exp t) := by
    rw [← sourceExitDomain_rebase m 1 ℓ j 0 z]
    change sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) z 0 ⊆ _
    rw [he, growingRecordExit]
    exact (root_domain_and_exit_inside z _ (Real.exp t) (by positivity) hzfit).1
  have hc := source_forward_count_eq_direct hF m 1 ℓ 0 ν (by norm_num)
    (by norm_num [sourceRecordBuffer]; exact hm16) (by omega) hdepth z
    (diskFinset (Real.exp t)) hzD 0 ω hfin
  exact hsum.trans hc.symm

end SRWTightness
