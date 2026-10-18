import SRWTightness.SourceForestApplicationGeometry
import SRWTightness.SourceProfileReturnRate
import SRWTightness.RootOuterDomainGeometry
import SRWTightness.CompetingEntranceLaw

namespace SRWTightness

/-- The level-zero source root has a uniform positive actual nonreturn mass at every exit. -/
theorem source_annular_nonreturn (hinput : PotentialKernelAsymptoticInput) :
    ∃ c T : ℝ, 0 < c ∧ ∀ t : ℝ, T ≤ t → ∀ b : Site,
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
      ∀ x ∈ domainExitBoundary (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0),
        c ≤ competingExitMass (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0) x := by
  obtain ⟨T₁, hlarge⟩ := source_outer_scale_large
  obtain ⟨T₂, hreturn⟩ := source_profile_return_rate hinput
  have hC : 0 < sourceRootReturnShift := by
    have h32 := Real.log_nonneg (show (1 : ℝ) ≤ 32 by norm_num)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    dsimp [sourceRootReturnShift]
    linarith
  refine ⟨1 / sourceRootReturnShift, max T₁ T₂, by positivity, ?_⟩
  intro t ht b hblo hbhi
  dsimp only
  intro x hx
  have hs := hlarge t ((le_max_left _ _).trans ht)
  have ht₂ : T₂ ≤ t := (le_max_right _ _).trans ht
  have hm := sourceLowerRadius_pos t
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) hs.1).2.2.1
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by nlinarith [hs.2]
  have hdepth := source_root_depth_pos (Real.exp t) (sourceLowerRadius t) hm hs.2
  have hg := source_annular_center_geometry (Real.exp t) (sourceLowerRadius t)
    hm70 hscale b hblo hbhi 0
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t) hm.le
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 (Nat.zero_le _)
  have hc : 0 ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 + 14 := by linarith
  have hd := root_domain_and_exit_inside b _ (Real.exp t) hc hg.2
  have hbuffer : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  have hx' : x ∈ domainExitBoundary (translateFinset b (diskFinset
      (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 + 14))) := by
    simpa only [sourceExitDomain, hbuffer] using hx
  have hxD : x ∈ diskFinset (Real.exp t) := hd.2 hx'
  have hxr := (translated_disk_boundary_radial b _ hc x hx').1
  have hbR : normSq b ≤ (Real.exp t) ^ 2 := by
    have hb := Real.sqrt_nonneg (normSq b)
    have hb2 := Real.sq_sqrt (normSq_nonneg b)
    have hR := Real.exp_pos t
    nlinarith
  have hr := hreturn t ht₂ (Real.exp t) hscale le_rfl 0 hdepth b x hbR hxD hxr
  have hKC := sourceEntranceDomain_subset_exit (sourceLowerRadius t) 1
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b 0 (by norm_num)
    (by rw [hbuffer]; linarith) (by omega)
  have hCD : sourceExitDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b 0 ⊆ diskFinset (Real.exp t) := by
    simpa only [sourceExitDomain, hbuffer] using hd.1
  rw [competingExitMass_eq_one_sub_hit _ _ (hKC.trans hCD)]
  simp only [Nat.cast_zero, zero_add] at hr
  linarith

end SRWTightness
