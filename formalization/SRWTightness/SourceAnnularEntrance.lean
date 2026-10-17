import SRWTightness.AnnulusFineEntranceBound
import SRWTightness.SourceForestApplicationGeometry
import SRWTightness.SourceRootReturnRate
import SRWTightness.RootOuterDomainGeometry
import SRWTightness.HitDomainMonotonicity

namespace SRWTightness

/-- The actual level-zero source root is entered with a uniform positive probability. -/
theorem source_annular_entrance (hinput : PotentialKernelAsymptoticInput) :
    ∃ c T : ℝ, 0 < c ∧ ∀ t : ℝ, T ≤ t → ∀ b : Site,
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      c ≤ setHitProbability (diskFinset (Real.exp t))
        (sourceEntranceDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b 0) 0 := by
  obtain ⟨K, A, hK, hA, hh⟩ := annulus_fine_entrance_bound hinput
  obtain ⟨T₀, hlarge⟩ := source_outer_scale_large
  have hg : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < sourceRootReturnShift := by
    have h32 := Real.log_nonneg (show (1 : ℝ) ≤ 32 by norm_num)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    dsimp [sourceRootReturnShift]
    linarith
  refine ⟨Real.log (3 / 2 : ℝ) / (2 * sourceRootReturnShift),
    max T₀ (max (A + 14) (14 + 2 * K / Real.log (3 / 2 : ℝ))), by positivity, ?_⟩
  intro t ht b hblo hbhi
  have hs := hlarge t ((le_max_left _ _).trans ht)
  have hmore := (le_max_right _ _).trans ht
  have htA : A + 14 ≤ t := (le_max_left _ _).trans hmore
  have htK : 14 + 2 * K / Real.log (3 / 2 : ℝ) ≤ t := (le_max_right _ _).trans hmore
  have hm := sourceLowerRadius_pos t
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) hs.1).2.2.1
  have hmt := sourceLowerRadius_ge_self t hs.1
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by nlinarith [hs.2]
  have hdepth := source_root_depth_pos (Real.exp t) (sourceLowerRadius t) hm hs.2
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  let a := sourceRecordRadius (sourceLowerRadius t) ℓ 1 - 14
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t) hm.le ℓ 1 (by
    dsimp [ℓ]; omega)
  have haA : A ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have haK : 2 * K / Real.log (3 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have hsmall : K / a ≤ Real.log (3 / 2 : ℝ) / 2 := by
    apply (div_le_iff₀ ha0).mpr
    have hhK := (div_le_iff₀ hg).mp haK
    nlinarith
  have hR := Real.exp_pos t
  have hbr := source_root_depth_bracket (Real.exp t) (sourceLowerRadius t) hm hscale
  have hmono := sourceRecordRadius_antitone (sourceLowerRadius t) hm.le ℓ
    (show 0 ≤ (1 : ℕ) by omega)
  have haR : a ≤ Real.exp t / 4 := by dsimp [a, ℓ] at *; linarith [hbr.1]
  have hlocal := hh a (Real.exp t / 2) (Real.exp t / 3) haA (by linarith)
    (by linarith) (-b) (by simpa only [normSq_neg] using haR.trans hblo)
    (by simpa only [normSq_neg] using hbhi)
  have hratio : (Real.exp t / 2) / (Real.exp t / 3) = (3 / 2 : ℝ) := by
    field_simp
  rw [hratio] at hlocal
  have hden : 0 < Real.log ((Real.exp t / 2) / a) :=
    Real.log_pos ((one_lt_div ha0).mpr (by linarith))
  have hlogupper := source_root_log_denominator (Real.exp t) (sourceLowerRadius t) 14 ℓ 0
    hm hR (by linarith) hbr.2.le
  have hdenC : Real.log ((Real.exp t / 2) / a) ≤ sourceRootReturnShift := by
    have hle := Real.log_le_log (div_pos (by positivity : 0 < Real.exp t / 2) ha0)
      (div_le_div_of_nonneg_right (by linarith : Real.exp t / 2 ≤ 2 * Real.exp t) ha0.le)
    dsimp [a] at hle
    simp only [Nat.cast_zero, zero_add] at hlogupper
    dsimp [sourceRootReturnShift]
    exact hle.trans (by linarith)
  have hlower : Real.log (3 / 2 : ℝ) / (2 * sourceRootReturnShift) ≤
      (Real.log (3 / 2 : ℝ) - K / a) / Real.log ((Real.exp t / 2) / a) := by
    calc
      _ = (Real.log (3 / 2 : ℝ) / 2) / sourceRootReturnShift := by ring
      _ ≤ (Real.log (3 / 2 : ℝ) / 2) / Real.log ((Real.exp t / 2) / a) :=
        div_le_div_of_nonneg_left (by positivity) hden hdenC
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hden.le
  have hfit : Real.sqrt (normSq b) + Real.exp t / 2 + 1 < Real.exp t := by linarith
  have hsub := (root_domain_and_exit_inside b (Real.exp t / 2) (Real.exp t)
    (by positivity) hfit).1
  have hdom := setHitProbability_mono_domain (translateFinset b (diskFinset (Real.exp t / 2)))
    (diskFinset (Real.exp t)) (translateFinset b (diskFinset a)) hsub 0
  have htrans : setHitProbability (translateFinset b (diskFinset (Real.exp t / 2)))
      (translateFinset b (diskFinset a)) 0 =
      setHitProbability (diskFinset (Real.exp t / 2)) (diskFinset a) (-b) := by
    simpa only [add_neg_cancel] using setHitProbability_translate b
      (diskFinset (Real.exp t / 2)) (diskFinset a) (-b)
  rw [htrans] at hdom
  have hbuffer : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  simpa only [sourceEntranceDomain, hbuffer, Nat.zero_add, a, ℓ] using
    (hlower.trans hlocal).trans hdom

end SRWTightness
