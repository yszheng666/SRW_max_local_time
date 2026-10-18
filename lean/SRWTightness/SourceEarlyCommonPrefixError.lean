import SRWTightness.SourceCommonGapForestError
import SRWTightness.SourceEarlyCommonObservation
import SRWTightness.SourceEarlyCommonNumericalError
import SRWTightness.SourcePrefixPopulationLevelCap

open Filter
namespace SRWTightness

/-- Equation 8.12 for the full common-prefix record error on the actual early gap. The prefix
barrier controls populations by the common depth rather than by the global time. -/
theorem source_early_common_prefix_error (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ρ := Real.sqrt (normSq (w - b))
      ∀ (M : Type*) (r : FiniteExcursionRecord M j),
      (∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      finiteRecordError
        (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceCommonPairInnerRadius t j) i))
        (fun _ ↦ 2 * (W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
          Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)))) j r ≤
        57 * (128 * B + 48 * Real.exp 1 * W) := by
  obtain ⟨Jmin, hobs⟩ := source_early_common_observation
  refine ⟨Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨aO, haO, hobs⟩ := hobs J₀ hJ₀
  obtain ⟨aE, haE, herror⟩ := source_early_common_numerical_error J₀
  obtain ⟨aL, hlevels⟩ := source_early_distance_levels J₀
  refine ⟨aO + aE + aL, by omega, ?_⟩
  filter_upwards [hobs, herror, hlevels, source_early_level_bounds,
    source_deficit_large_conditions] with t ho he hl ht hlarge
  intro b w hbw ha hrange
  dsimp only
  let ρ := Real.sqrt (normSq (w - b))
  let a := sourceCommonPairDistanceIndex t ρ
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  change aO + aE + aL ≤ a at ha
  have haO' : aO ≤ a := by omega
  have haE' : aE ≤ a := by omega
  have haL : aL ≤ a := by omega
  have hlevels := hl a haL hrange
  have hJ : J ≤ a := by have hp := hlevels.1; change 0 < a - J at hp; omega
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by
    have hv := hlevels.2.2
    dsimp [j]
    omega
  obtain ⟨hρone, hsep, _, _, _⟩ := ho b w hbw haO' hrange
  have hρ : 1 ≤ ρ := by
    have hn := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    have hs := Real.sq_sqrt (normSq_nonneg (w - b))
    have hp := Real.sqrt_nonneg (normSq (w - b))
    dsimp [ρ]
    nlinarith
  have hρ0 : 0 < ρ := by linarith
  have hr0 : 0 < sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 := by
    unfold sourceRecordRadius
    exact mul_pos (sourceLowerRadius_pos t) (Real.exp_pos _)
  have hlog : 1 ≤ Real.log (sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 / ρ) :=
    (Nat.one_le_floor_iff _).mp (haO.trans haO')
  have hexp := Real.exp_le_exp.mpr (show 0 ≤ Real.log
    (sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 / ρ) by linarith)
  rw [Real.exp_zero, Real.exp_log (div_pos hr0 hρ0)] at hexp
  have houter := (one_le_div hρ0).mp hexp
  intro M r hbar
  have hpop := source_prefix_population_level_cap t j
    (sourceBarrierSlope_bounds t hlarge.1 hlarge.2.1) (ht.2 j hj).2.2 M r hbar
  have hf := source_common_gap_forest_error B W 8 t ρ j J j hB hW (by norm_num)
    hρ houter (Nat.sub_add_cancel hJ) (by linarith) [r] (by
      intro i hi
      simpa only [forestLevelPopulation, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero] using hpop i hi)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hf
  let K := 128 * B + 48 * Real.exp 1 * W
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm := sourceCommonPairInnerRadius_pos t j
  have hc₀ : 128 * B ≤ K := by
    exact le_add_of_nonneg_right (by positivity)
  have hc₁ : 48 * Real.exp 1 * W ≤ K := by dsimp [K]; linarith
  have hb₀ := mul_le_mul_of_nonneg_right hc₀
    (show 0 ≤ ((j : ℝ) + 1) ^ 2 * (14 / sourceCommonPairInnerRadius t j) by positivity)
  have hb₁ := mul_le_mul_of_nonneg_right hc₁
    (show 0 ≤ ((j : ℝ) + 1) ^ 2 * (((J : ℝ) + 1) * Real.exp (-(J : ℝ))) by positivity)
  have hn := (he a haE' hrange).1.trans (he a haE' hrange).2
  change ((j : ℝ) + 1) ^ 2 * (14 / sourceCommonPairInnerRadius t j +
    ((J : ℝ) + 1) * Real.exp (-(J : ℝ))) ≤ 57 at hn
  have htotal := mul_le_mul_of_nonneg_left hn hK
  apply hf.trans
  change _ ≤ 57 * K
  calc
    _ = 128 * B * (((j : ℝ) + 1) ^ 2 * (14 / sourceCommonPairInnerRadius t j)) +
        48 * Real.exp 1 * W *
          (((j : ℝ) + 1) ^ 2 * (((J : ℝ) + 1) * Real.exp (-(J : ℝ)))) := by ring
    _ ≤ K * (((j : ℝ) + 1) ^ 2 * (14 / sourceCommonPairInnerRadius t j)) +
        K * (((j : ℝ) + 1) ^ 2 * (((J : ℝ) + 1) * Real.exp (-(J : ℝ)))) :=
      add_le_add hb₀ hb₁
    _ = K * (((j : ℝ) + 1) ^ 2 * (14 / sourceCommonPairInnerRadius t j +
        ((J : ℝ) + 1) * Real.exp (-(J : ℝ)))) := by ring
    _ ≤ K * 57 := htotal
    _ = 57 * K := by ring

end SRWTightness
