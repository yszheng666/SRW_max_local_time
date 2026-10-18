import SRWTightness.SourceEarlyCommonObservation
import SRWTightness.SourceEarlyTerminalErrorSmall

open Filter

namespace SRWTightness

/-- All terminal hypotheses for the ordered record comparison hold on the early distance gap. -/
theorem source_early_ordered_conditions (B W T M : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let j := a - sourceEarlyDistanceGap a J₀
      let m := sourceCommonPairInnerRadius t j
      let R := 2 * Real.sqrt (normSq (w - b))
      112 ≤ m ∧ T ≤ m - 14 ∧ M ≤ m ∧ B * 14 / m ≤ 1 / 4 ∧
      0 < R ∧ 2 * R < m - 14 - 2 ∧
      sourceCommonPairIntensity t j * capacity (sourceCommonPairDomain t b j)
        (sourceCommonPairObservation b w) ≤ 1 / 2 ∧
      W * (R + 1) / m * Real.log (m / R) ≤ 1 / 2 := by
  obtain ⟨JO, hobs⟩ := source_early_common_observation
  refine ⟨max JO ⌈Real.log 8 + 1⌉₊, ?_⟩
  intro J₀ hJ₀
  obtain ⟨aO, haO, ho⟩ := hobs J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨aL, hl⟩ := source_early_distance_levels J₀
  refine ⟨aO + aL + ⌈6 * Real.exp 1 * W⌉₊, by omega, ?_⟩
  filter_upwards [ho, hl, source_early_level_bounds,
    sourceLowerRadius_tendsto_atTop.eventually
      (eventually_ge_atTop (max 112 (max (T + 14) (max M (56 * B)))))]
    with t ho hl ht hscale
  intro b w hbw ha hrange
  dsimp only
  let ρ := Real.sqrt (normSq (w - b))
  let a := sourceCommonPairDistanceIndex t ρ
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let m := sourceCommonPairInnerRadius t j
  change aO + aL + ⌈6 * Real.exp 1 * W⌉₊ ≤ a at ha
  have haO' : aO ≤ a := by omega
  have hlevels := hl a (show aL ≤ a by omega) hrange
  have hJ : J ≤ a := by have hh := hlevels.1; change 0 < a - J at hh; omega
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by
    have hh := hlevels.2.2
    dsimp [j]
    omega
  have hm := hscale.trans (sourceCommonPairInnerRadius_ge_lower t j (ht.2 j hj).1)
  have hm112 : 112 ≤ m := (le_max_left _ _).trans hm
  have hmT : T + 14 ≤ m := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hm
  have hmM : M ≤ m :=
    (le_trans (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))).trans hm
  have hmB : 56 * B ≤ m :=
    (le_trans (le_max_right _ _) ((le_max_right _ _).trans (le_max_right _ _))).trans hm
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
  have hJlower : Real.log 8 + 1 ≤ (J : ℝ) := by
    have hceil := Nat.le_ceil (Real.log 8 + 1)
    have hc : ⌈Real.log 8 + 1⌉₊ ≤ J := by
      have hx := (le_max_right JO ⌈Real.log 8 + 1⌉₊).trans hJ₀
      dsimp [J, sourceEarlyDistanceGap]
      omega
    exact hceil.trans (Nat.cast_le.mpr hc)
  have hbr := (source_common_pair_log_separation t ρ hρ0 houter j J
    (Nat.sub_add_cancel hJ)).1
  have hm0 : 0 < m := by linarith
  have h8 : 8 * ρ ≤ m := by
    apply (Real.log_le_log_iff (by positivity) hm0).mp
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hρ0.ne']
    change (J : ℝ) - 1 ≤ Real.log m - Real.log ρ at hbr
    linarith
  obtain ⟨_, _, _, _, hcap⟩ := ho b w hbw haO' hrange
  have hlarge : 6 * Real.exp 1 * W ≤ ((a : ℝ) + 1) ^ 2 := by
    have hc := (Nat.le_ceil (6 * Real.exp 1 * W)).trans
      (Nat.cast_le.mpr (show ⌈6 * Real.exp 1 * W⌉₊ ≤ a by omega))
    nlinarith [sq_nonneg (a : ℝ)]
  have herr := source_early_terminal_error_small W t ρ a J₀ hW hρ houter rfl hJ
    (by change 2 * ρ ≤ m; linarith) hlarge
  refine ⟨hm112, by linarith, hmM, ?_, by linarith, by linarith, hcap, herr⟩
  apply (div_le_iff₀ hm0).mpr
  nlinarith

end SRWTightness
