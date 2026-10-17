import SRWTightness.SourcePairLongRadius
import SRWTightness.SourceEarlyLongEscape
import SRWTightness.SourceForestApplicationGeometry
import SRWTightness.SourceCandidateAnnulus
import SRWTightness.SeparatedDiskExit

open Filter
namespace SRWTightness

/-- The actual early source long balls satisfy the nesting, one-step separation and origin exclusion
needed for exterior bridge factorization, once nu has the manuscript distance-scale form. -/
theorem source_exterior_geometry :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      K b ⊆ C b ∧ K w ⊆ C w ∧ C b ∪ C w ⊆ diskFinset (Real.exp t) ∧
        (∀ y ∈ domainExitBoundary (C b), y ∉ C w) ∧
        (∀ y ∈ domainExitBoundary (C w), y ∉ C b) ∧ 0 ∉ C b ∪ C w := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (60 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t ht hN htime hm60 ht0
  intro b w ν J hb hw hbw ha hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := Real.sqrt (normSq (w - b))
  let r := sourceRecordRadius m ℓ (ν - J)
  let B := r + 14
  have hm : 0 < m := sourceLowerRadius_pos t
  have hscale : 32 * m ≤ Real.exp t := by
    have hh := (hT t ht).2
    change 32 * sourceLowerRadius t ≤ Real.exp t
    nlinarith [Real.exp_one_gt_two, sourceLowerRadius_pos t]
  have hbr := (source_root_depth_bracket (Real.exp t) m hm hscale).1
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hνℓ : ν + 1 ≤ ℓ := by
    have hpos : 0 < ℓ - 1 := hN.1
    omega
  have hρ : 0 < ρ := by
    have hh := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    exact Real.sqrt_pos.2 (by linarith)
  have hr0 : 0 < sourceRecordRadius m ℓ 0 := by unfold sourceRecordRadius; positivity
  have hlog : 1 ≤ Real.log (sourceRecordRadius m ℓ 0 / ρ) :=
    (Nat.one_le_floor_iff _).mp ha
  have houter : ρ ≤ sourceRecordRadius m ℓ 0 := by
    have he := Real.exp_le_exp.mpr (show 0 ≤ Real.log (sourceRecordRadius m ℓ 0 / ρ) by linarith)
    rw [Real.exp_zero, Real.exp_log (div_pos hr0 hρ)] at he
    exact (one_le_div hρ).mp he
  have hrbound : r < Real.exp (-4) * ρ := source_pair_long_radius t ρ hρ houter ν J hform
  have hrlo : m ≤ r := sourceRecordRadius_ge_terminal m hm.le ℓ (ν - J) (by omega)
  have he4 : Real.exp (-4) ≤ (1 / 5 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (a := (5 : ℝ)) (b := Real.exp 4) (by norm_num)
        (by linarith [Real.add_one_le_exp (4 : ℝ)]))
  have hrρ : r < ρ / 5 := by
    have hh := mul_le_mul_of_nonneg_right he4 hρ.le
    nlinarith
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have hgap : B + B + 1 ≤ ρ := by dsimp [B]; change 60 ≤ m at hm60; linarith
  have hmono := sourceRecordRadius_antitone m hm.le ℓ (Nat.zero_le (ν - J))
  have hBupper : B ≤ Real.exp t / 32 + 14 := by dsimp [B, r]; linarith
  have hRlarge : 1920 ≤ Real.exp t := by change 60 ≤ m at hm60; linarith
  have hdomain (z : Site) : sourceExitDomain m 1 ℓ z (ν - J) =
      translateFinset z (diskFinset B) := by
    norm_num [sourceExitDomain, sourceRecordBuffer, B, r]
  have hinner (z : Site) : sourceEntranceDomain m 1 ℓ z ν ⊆ sourceExitDomain m 1 ℓ z (ν - J) := by
    have hs := sourceEntranceDomain_subset_exit m 1 ℓ z ν (by norm_num)
      (by norm_num [sourceRecordBuffer]; change 60 ≤ m at hm60; linarith) hνℓ
    have hrad := sourceRecordRadius_antitone m hm.le ℓ (Nat.sub_le ν J)
    have hshort : 0 ≤ sourceRecordRadius m ℓ ν + 14 := by unfold sourceRecordRadius; positivity
    have hnest : sourceExitDomain m 1 ℓ z ν ⊆ sourceExitDomain m 1 ℓ z (ν - J) := by
      unfold sourceExitDomain sourceRecordBuffer
      norm_num only
      exact Finset.image_subset_image (diskFinset_mono _ _ hshort (by linarith))
    exact hs.trans hnest
  have hfit (z : Site) (hz : z ∈ sourceCandidateAnnulus (Real.exp t)) :
      sourceExitDomain m 1 ℓ z (ν - J) ⊆ diskFinset (Real.exp t) ∧
        0 ∉ sourceExitDomain m 1 ℓ z (ν - J) := by
    have hzc := (mem_sourceCandidateAnnulus (Real.exp t) (Real.exp_pos _) z).mp hz
    rw [hdomain]
    refine ⟨(root_domain_and_exit_inside z B (Real.exp t) hB0 (by linarith)).1, ?_⟩
    intro hz0
    have hnorm : normSq z < B ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq,
        zero_sub, normSq_neg] using hz0
    have hsq := normSq_eq_sq_sqrt z
    have hnon := Real.sqrt_nonneg (normSq z)
    nlinarith
  have hbfit := hfit b hb
  have hwfit := hfit w hw
  refine ⟨hinner b, hinner w, Finset.union_subset hbfit.1 hwfit.1, ?_, ?_, ?_⟩
  · change ∀ y ∈ domainExitBoundary (sourceExitDomain m 1 ℓ b (ν - J)),
      y ∉ sourceExitDomain m 1 ℓ w (ν - J)
    rw [hdomain b, hdomain w]
    exact translated_disk_exit_gap b w B B hB0 hB0 hgap
  · have hgap' : B + B + 1 ≤ Real.sqrt (normSq (b - w)) := by
      simpa only [show b - w = -(w - b) by abel, normSq_neg] using hgap
    change ∀ y ∈ domainExitBoundary (sourceExitDomain m 1 ℓ w (ν - J)),
      y ∉ sourceExitDomain m 1 ℓ b (ν - J)
    rw [hdomain w, hdomain b]
    exact translated_disk_exit_gap w b B B hB0 hB0 hgap'
  · simpa only [Finset.mem_union, not_or] using And.intro hbfit.2 hwfit.2

end SRWTightness
