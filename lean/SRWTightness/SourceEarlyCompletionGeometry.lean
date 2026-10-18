import SRWTightness.DiskExitOutsideOther
import SRWTightness.SourceEarlyLongBallDisjoint
import SRWTightness.SourceEarlyRootObservationGeometry
import SRWTightness.RootBinomialMoment

open Filter
namespace SRWTightness

/-- Both short completion boundaries are restart states outside both short outer domains. -/
theorem source_early_completion_geometry :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ), b ≠ w →
      1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let Cb := sourceExitDomain m 1 ℓ b ν
      let Cw := sourceExitDomain m 1 ℓ w ν
      Disjoint Cb Cw ∧ ∀ x ∈ rootCompletionSet Cb Cw,
        x ∈ sourceCommonPairObservation b w ∧ x ∉ Cb ∧ x ∉ Cw := by
  filter_upwards [source_early_level_bounds, source_early_root_observation_geometry,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ))]
    with t ht hgeo hm16
  intro b w ν J hbw ha hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := Real.sqrt (normSq (w - b))
  let r := sourceRecordRadius m ℓ ν
  have hm : 0 < m := sourceLowerRadius_pos t
  have hdepth : ν + 1 ≤ ℓ := (ht.2 ν hν).1
  have hrad : m ≤ r := sourceRecordRadius_ge_terminal m hm.le ℓ ν (by omega)
  have hρ : 0 < ρ := by
    have hn := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    exact Real.sqrt_pos.mpr (by linarith)
  have hr0 : 0 < sourceRecordRadius m ℓ 0 := by unfold sourceRecordRadius; positivity
  have hlog : 1 ≤ Real.log (sourceRecordRadius m ℓ 0 / ρ) :=
    (Nat.one_le_floor_iff _).mp ha
  have he := Real.exp_le_exp.mpr (show 0 ≤ Real.log
    (sourceRecordRadius m ℓ 0 / ρ) by linarith)
  rw [Real.exp_zero, Real.exp_log (div_pos hr0 hρ)] at he
  have houter := (one_le_div hρ).mp he
  have hsmall := (sourceRecordRadius_antitone m hm.le ℓ (Nat.sub_le ν J)).trans_lt
    (source_pair_long_radius t ρ hρ houter ν J hform)
  have he4 : Real.exp (-4) ≤ (1 / 5 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (a := (5 : ℝ)) (b := Real.exp 4) (by norm_num)
        (by linarith [Real.add_one_le_exp (4 : ℝ)])
  have hrρ : r < ρ / 5 := by
    have hh := mul_le_mul_of_nonneg_right he4 hρ.le
    change r < Real.exp (-4) * ρ at hsmall
    nlinarith
  have hm16' : 16 ≤ m := hm16
  have hsep : 2 * (r + 14) + 1 < ρ := by linarith
  have hsym : Real.sqrt (normSq (b - w)) = ρ := by
    rw [show b - w = -(w - b) by abel, normSq_neg]
  have hdom (z : Site) : sourceExitDomain m 1 ℓ z ν =
      translateFinset z (diskFinset (r + 14)) := by
    norm_num [sourceExitDomain, sourceRecordBuffer, r]
  constructor
  · rw [hdom b, hdom w]
    apply translated_disks_disjoint b w _ _ (by linarith) (by linarith)
    change (r + 14) + (r + 14) ≤ ρ
    linarith
  intro x hx
  rcases hx with hx | hx
  · have hb := (hgeo b w ν J hbw ha hν hform b (by simp)).2.2 hx
    refine ⟨hb, hx.1, ?_⟩
    rw [hdom b] at hx
    rw [hdom w]
    exact disk_exit_outside_other b w x (r + 14) (by linarith) hsep hx
  · have hw := (hgeo b w ν J hbw ha hν hform w (by simp)).2.2 hx
    refine ⟨hw, ?_, hx.1⟩
    rw [hdom w] at hx
    rw [hdom b]
    apply disk_exit_outside_other w b x (r + 14) (by linarith) _ hx
    simpa only [hsym] using hsep

end SRWTightness
