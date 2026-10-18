import SRWTightness.SourceAnnularEntrance
import SRWTightness.SourceAnnularNonreturn
import SRWTightness.SourceProfileSingleRoot
import SRWTightness.ActualSingleRootComparison
import SRWTightness.GeneralEntranceRadialSupport

open MeasureTheory

namespace SRWTightness

/-- Actual source records with exactly one level-zero root satisfy a uniform two-sided bound. -/
theorem source_annular_single_root (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W c T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 0 < c ∧
    ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ ℓ : ℕ, ℓ = sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let n := ℓ - 1
      let η := finiteRecordError
        (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) i))
        (fun _ : Mark K ↦ 2 * (W * (a + 1) / sourceLowerRadius t *
          Real.log (sourceLowerRadius t / a))) n
      let Q := finiteRecordReferenceWeight (fun v ↦
        (referenceMarkLaw
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
          (sourceReferenceIntensity (sourceLowerRadius t) 14)).real {v}) n
      ∀ r : FiniteExcursionRecord (Mark K) n,
      let p := pathLaw.real {ω |
        (killedChildIntervals (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0 ω).length = 1 ∧
        killedChildRecords (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n) ω = [r]}
      c * Real.exp (-η r) * Q r ≤ p ∧ p ≤ Real.exp (η r) * Q r := by
  obtain ⟨B, W, T₀, hB, hW, hrecord⟩ := source_profile_single_root_comparison hinput
  obtain ⟨c₁, T₁, hc₁, hfirst⟩ := source_annular_entrance hinput
  obtain ⟨c₂, T₂, hc₂, hlast⟩ := source_annular_nonreturn hinput
  obtain ⟨T₃, hlarge⟩ := source_outer_scale_large
  refine ⟨B, W, c₁ * c₂, max (max T₀ T₁) (max T₂ T₃), hB, hW,
    mul_pos hc₁ hc₂, ?_⟩
  intro b t a K ht ha hcut hK hblo hbhi ℓ hℓ
  dsimp only
  intro r
  have ht₀ : T₀ ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have ht₁ : T₁ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have ht₂ : T₂ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht₃ : T₃ ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hs := hlarge t ht₃
  have hm := sourceLowerRadius_pos t
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) hs.1).2.2.1
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by nlinarith [hs.2]
  have hdepth : 0 < ℓ := by
    rw [hℓ]
    exact source_root_depth_pos (Real.exp t) (sourceLowerRadius t) hm hs.2
  have hg := source_annular_center_geometry (Real.exp t) (sourceLowerRadius t)
    hm70 hscale b hblo hbhi 0
  rw [← hℓ] at hg
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t) hm.le ℓ 1 (by omega)
  have hmono := sourceRecordRadius_antitone (sourceLowerRadius t) hm.le ℓ
    (show 0 ≤ (1 : ℕ) by omega)
  have hbuffer : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  let A := sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0
  let C := sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0
  let radius := sourceRecordRadius (sourceLowerRadius t) ℓ 1 - 14
  have hA : A = translateFinset b (diskFinset radius) := by
    simp only [A, radius, sourceEntranceDomain, hbuffer, Nat.zero_add]
  have har : 1 ≤ radius := by dsimp [radius]; linarith
  have hAC : A ⊆ C := sourceEntranceDomain_subset_exit _ _ _ _ _ (by norm_num)
    (by rw [hbuffer]; linarith) (by omega)
  have hCD : C ⊆ diskFinset (Real.exp t) := by
    have hh := (root_domain_and_exit_inside b
      (sourceRecordRadius (sourceLowerRadius t) ℓ 0 + 14) (Real.exp t)
      (by linarith) hg.2).1
    simpa only [C, sourceExitDomain, hbuffer] using hh
  have hx : (0 : Site) ∈ diskFinset (Real.exp t) \ A := by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (mem_diskFinset (Real.exp t) 0).mpr
      simpa [disk, normSq] using sq_pos_of_pos (Real.exp_pos t)
    · intro hz
      rw [hA] at hz
      have hh : normSq b < radius ^ 2 := by
        simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq,
          zero_sub, normSq_neg] using hz
      have hb2 := Real.sq_sqrt (normSq_nonneg b)
      have hb0 := Real.sqrt_nonneg (normSq b)
      have hradb : radius ≤ Real.sqrt (normSq b) := hg.1
      nlinarith
  let S : Set Site := {z | z ∈ A ∧ radius - 1 ≤ Real.sqrt (normSq (z - b)) ∧
    Real.sqrt (normSq (z - b)) ≤ radius}
  have hsupport : ∀ᵐ z ∂competingEntranceLaw (diskFinset (Real.exp t)) A 0, z ∈ S := by
    have hradial := competingEntranceLaw_radial_support_domain
      (diskFinset (Real.exp t)) b radius har 0 (by simpa only [← hA] using hx)
    rw [← hA] at hradial
    filter_upwards [competingEntranceLaw_supported (diskFinset (Real.exp t)) A 0,
      hradial] with z hz hr
    exact ⟨hz, hr⟩
  apply actual_single_root_comparison (diskFinset (Real.exp t)) A C hAC hCD _ S
    (fun z hz ↦ hz.1) 0 hsupport r c₁ c₂ _ _ hc₂.le
  · apply finiteRecordReferenceWeight_nonneg
    intro v
    exact measureReal_nonneg
  · simpa only [A, ← hℓ] using hfirst t ht₁ b hblo hbhi
  · intro y hy
    have hh := hlast t ht₂ b hblo hbhi
    dsimp only at hh
    rw [← hℓ] at hh
    exact hh y hy
  · intro z hz
    have hh := hrecord b t a K ht₀ ha hcut hK ℓ 0 hdepth z r hz.2.1 hz.2.2
    simpa only [sourceReferenceIntensity, C] using hh

end SRWTightness
