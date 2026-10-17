import SRWTightness.SourceGeneralAnnularGeometry
import SRWTightness.SourceRootReturnRate
import SRWTightness.RootOuterDomainGeometry
import SRWTightness.CompetingEntranceLaw

namespace SRWTightness

/-- General source scales have a uniform positive final nonreturn mass at every root exit. -/
theorem source_general_annular_nonreturn (hinput : PotentialKernelAsymptoticInput) :
    ∃ c A : ℝ, 0 < c ∧ ∀ (R m H : ℝ), A ≤ m - H → 0 ≤ H → 2 * H ≤ m →
      32 * Real.exp 1 * m ≤ R → ∀ b : Site,
      R / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ R / 3 →
      let ℓ := sourceRootDepth R m
      ∀ x ∈ domainExitBoundary
        (translateFinset b (diskFinset (sourceRecordRadius m ℓ 0 + H))),
      c ≤ competingExitMass (diskFinset R)
        (translateFinset b (diskFinset (sourceRecordRadius m ℓ 1 - H))) x := by
  obtain ⟨K, A, hK, hA, hh⟩ := source_root_return_rate hinput
  have hC : 0 < sourceRootReturnShift := by
    have h32 := Real.log_nonneg (show (1 : ℝ) ≤ 32 by norm_num)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    dsimp [sourceRootReturnShift]
    linarith
  refine ⟨1 / sourceRootReturnShift, max 2 (max A (K * sourceRootReturnShift)),
    by positivity, ?_⟩
  intro R m H hmH hH hhalf hscale b hblo hbhi
  dsimp only
  intro x hx
  have hm2 : 2 ≤ m - H := (le_max_left _ _).trans hmH
  have htA : A ≤ m - H := (le_max_left _ _).trans ((le_max_right _ _).trans hmH)
  have htK : K * sourceRootReturnShift ≤ m - H :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hmH)
  have hm : 0 < m := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase : 32 * m ≤ R := by nlinarith
  have hR : 0 < R := by linarith
  have hdepth := source_root_depth_pos R m hm hscale
  let ℓ := sourceRootDepth R m
  have hrad := sourceRecordRadius_ge_terminal m hm.le ℓ 1 (by dsimp [ℓ]; omega)
  have hrad0 := sourceRecordRadius_ge_terminal m hm.le ℓ 0 (Nat.zero_le _)
  have hmono := sourceRecordRadius_antitone m hm.le ℓ (show 0 ≤ (1 : ℕ) by omega)
  have hbr := source_root_depth_bracket R m hm hbase
  have hg := source_general_annular_geometry R m H (by linarith) hH (by linarith)
    hbase b hblo hbhi 0
  have hc : 0 ≤ sourceRecordRadius m ℓ 0 + H := by linarith
  have hd := root_domain_and_exit_inside b _ R hc hg.2
  have hxD : x ∈ diskFinset R := hd.2 hx
  have hxr := (translated_disk_boundary_radial b _ hc x hx).1
  have hbR : normSq b ≤ R ^ 2 := by
    have hb := Real.sqrt_nonneg (normSq b)
    have hb2 := Real.sq_sqrt (normSq_nonneg b)
    nlinarith
  have hr := hh R m H ℓ 0 hm hR hH (by linarith) hbr.2.le
    (by linarith) (by dsimp [ℓ] at *; linarith [hbr.1])
    (by simpa only [Nat.cast_zero, zero_add] using
      htK.trans (show m - H ≤ sourceRecordRadius m ℓ 1 - H by linarith))
    b x hbR hxD hxr
  have hAC : translateFinset b (diskFinset (sourceRecordRadius m ℓ 1 - H)) ⊆
      translateFinset b (diskFinset (sourceRecordRadius m ℓ 0 + H)) := by
    intro y hy
    rw [mem_translateFinset_iff] at hy ⊢
    exact diskFinset_mono _ _ (by linarith) (by linarith) hy
  rw [competingExitMass_eq_one_sub_hit _ _ (hAC.trans hd.1)]
  simp only [Nat.cast_zero, zero_add] at hr
  linarith

end SRWTightness
