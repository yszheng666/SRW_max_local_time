import SRWTightness.SourceLocalTimeObservation
import SRWTightness.SourceForestApplicationGeometry
import SRWTightness.RootOuterDomainGeometry
import SRWTightness.DiskCapacityLogBound

open Filter

namespace SRWTightness

/-- The manuscript observation cutoff lies inside the terminal visit-coverage disk. -/
theorem source_observation_coverage_radius (t a : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (ha : 1 ≤ a) (hcut : a ≤ sourceLowerRadius t / t ^ 6) :
    a ≤ sourceLowerRadius t - sourceRecordBuffer 1 - 2 := by
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hp : (2 : ℝ) ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) ht2 6
  norm_num at hp
  have hmul := (le_div_iff₀ (pow_pos ht0 6)).mp hcut
  have ha0 : 0 ≤ a := by linarith
  have hh := mul_le_mul_of_nonneg_left hp ha0
  norm_num [sourceRecordBuffer]
  nlinarith

/-- Actual annular centers and source cutoffs satisfy all geometric premises of local-time observation recovery. -/
theorem source_annular_local_observation :
    ∃ T : ℝ, ∀ (t : ℝ), T ≤ t → ∀ (b : Site) (a : ℝ) (K : Finset Site),
      1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 → K ⊆ translateFinset b (diskFinset a) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ n : ℕ, n + 1 = sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (ω : Sample), domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ →
      ∀ r : FiniteExcursionRecord (Mark K) n,
      killedChildRecords (diskFinset (Real.exp t))
        (sourceEntranceDomain (sourceLowerRadius t) 1 (n + 1) b 0)
        (sourceExitDomain (sourceLowerRadius t) 1 (n + 1) b 0) 0
        (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 (n + 1) b)
          (sourceTreeExit (sourceLowerRadius t) 1 (n + 1) b) (wordOccupationMark K) n) ω = [r] →
      ∀ (q : ℕ) (Dref : Finset Site) (family : Fin q → Finset Site) (z : K)
        (α g u : ℝ) (i : Option (Fin q)),
      let k := geometricGWPopulation (finiteRecordPopulationList n r) n
      normalizedObservation Dref K family z k α g u i
        (terminalListSamples 0 k (finiteRecordLeaves n r)) =
        domainLocalObservation Dref K family z (diskFinset (Real.exp t)) 0 ω k α g u i := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  refine ⟨T, ?_⟩
  intro t ht b a K ha hcut hK hblo hbhi n hn ω hfin r hr q Dref family z α g u i
  have hs := hT t ht
  have hm0 := sourceLowerRadius_pos t
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) hs.1).2.2.1
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by nlinarith [hs.2]
  have hrad := source_observation_coverage_radius t a hs.1 ha hcut
  have hobs : K ⊆ translateFinset b
      (diskFinset (sourceLowerRadius t - sourceRecordBuffer 1 - 2)) := by
    intro y hy
    apply (mem_translateFinset_iff _ _ _).mpr
    exact diskFinset_mono _ _ (by linarith) hrad
      ((mem_translateFinset_iff _ _ _).mp (hK hy))
  have hg := (source_annular_center_geometry (Real.exp t) (sourceLowerRadius t)
    hm70 hscale b hblo hbhi 0).2
  rw [← hn] at hg
  have hbuffer : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  have hroot : sourceExitDomain (sourceLowerRadius t) 1 (n + 1) b 0 ⊆
      diskFinset (Real.exp t) := by
    have hpos : 0 ≤ sourceRecordRadius (sourceLowerRadius t) (n + 1) 0 + 14 := by
      unfold sourceRecordRadius
      positivity
    simpa only [sourceExitDomain, hbuffer] using
      (root_domain_and_exit_inside b _ (Real.exp t) hpos hg).1
  exact source_single_root_normalized_observation (sourceLowerRadius t) 1 n b
    (diskFinset (Real.exp t)) K 0 (by norm_num) (by rw [hbuffer]; linarith)
    hobs hroot ω hfin r hr Dref family z α g u i

end SRWTightness
