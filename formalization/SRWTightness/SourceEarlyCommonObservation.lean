import SRWTightness.SourceEarlyLevelBounds
import SRWTightness.SourceEarlyDistanceLevels
import SRWTightness.SourceCommonPairDistanceChernoff
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.SourceTerminalCapacityHalf

open Filter
namespace SRWTightness

/-- The actual distance-dependent early gap supplies the observation geometry and normalization
for the common reference mark. The lower gap threshold is fixed independently of time. -/
theorem source_early_common_observation :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ρ := Real.sqrt (normSq (w - b))
      1 ≤ 2 * ρ ∧ 2 * (2 * ρ) ≤ sourceCommonPairInnerRadius t j ∧
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
        Real.log (sourceCommonPairInnerRadius t j) - Real.log (2 * ρ) ∧
      sourceCommonPairObservation b w ⊆ sourceCommonPairDomain t b j ∧
      sourceCommonPairIntensity t j * capacity (sourceCommonPairDomain t b j)
        (sourceCommonPairObservation b w) ≤ 1 / 2 := by
  let L₁ := Real.log 4 + 1
  let L₂ := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 + Real.log 2 + 1
  refine ⟨⌈max L₁ L₂⌉₊, ?_⟩
  intro J₀ hJ₀
  have hthreshold : max L₁ L₂ ≤ (J₀ : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hJ₀)
  obtain ⟨a₀, ha₀, hgap⟩ := source_early_distance_gap_small J₀
  obtain ⟨a₁, hlevels⟩ := source_early_distance_levels J₀
  refine ⟨max a₀ a₁, ha₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [hlevels, source_early_level_bounds,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (70 : ℝ))]
    with t hl ht hm
  intro b w hbw ha hrange
  dsimp only
  let ρ := Real.sqrt (normSq (w - b))
  let a := sourceCommonPairDistanceIndex t ρ
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  have hρ : 1 ≤ ρ := by
    have hn := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    have hs := Real.sq_sqrt (normSq_nonneg (w - b))
    have hp := Real.sqrt_nonneg (normSq (w - b))
    dsimp [ρ]
    nlinarith
  have hρ0 : 0 < ρ := by linarith
  have hJ : J ≤ a := by have hh := hgap a ((le_max_left _ _).trans ha); omega
  have ha1 : 1 ≤ a := ha₀.trans ((le_max_left _ _).trans ha)
  have hν := (hl a ((le_max_right _ _).trans ha) hrange).2.2
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by dsimp [j]; omega
  have hmj := hm.trans (sourceCommonPairInnerRadius_ge_lower t j (ht.2 j hj).1)
  have hr0 : 0 < sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 := by
    unfold sourceRecordRadius
    positivity
  have hlog : 1 ≤ Real.log (sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 / ρ) :=
    (Nat.one_le_floor_iff _).mp ha1
  have he := Real.exp_le_exp.mpr (show 0 ≤ Real.log
    (sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 / ρ) by linarith)
  rw [Real.exp_zero, Real.exp_log (div_pos hr0 hρ0)] at he
  have houter := (one_le_div hρ0).mp he
  have hJr : (J₀ : ℝ) ≤ J := Nat.cast_le.mpr
    (show J₀ ≤ J by dsimp [J, sourceEarlyDistanceGap]; omega)
  have hs := source_common_pair_observation_separation t ρ hρ0 houter j J
    (Nat.sub_add_cancel hJ)
    (((le_max_left L₁ L₂).trans hthreshold).trans hJr)
    (((le_max_right L₁ L₂).trans hthreshold).trans hJr)
  have hKD : sourceCommonPairObservation b w ⊆ sourceCommonPairDomain t b j := by
    rw [sourceCommonPairDomain_eq]
    apply Finset.image_subset_image
    apply diskFinset_mono _ _ (by linarith : 0 ≤ 2 * ρ)
    have hr := sourceCommonPairInnerRadius_pos t j
    nlinarith [Real.exp_one_gt_two]
  have hcap := source_terminal_capacity_half b (sourceCommonPairInnerRadius t j) 14
    (2 * ρ) (sourceCommonPairObservation b w) (by linarith) hs.1 (by norm_num)
    (by linarith) (Finset.Subset.refl _) hs.2
  rw [← sourceCommonPairDomain_eq] at hcap
  exact ⟨by linarith, hs.1, hs.2, hKD, hcap⟩

end SRWTightness
