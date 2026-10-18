import SRWTightness.SourceEarlyRootObservationGeometry

open Filter
namespace SRWTightness

/-- Both logarithmic separation denominators dominate half the short unbuffered radius. -/
theorem source_early_short_gaps :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ), b ≠ w →
      1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let r := sourceRecordRadius m ℓ ν
      let a := sourceRecordRadius m ℓ (ν + 1) - 14
      0 ≤ a ∧ r / 2 ≤ (r + 14) - a ∧
        r / 2 ≤ Real.sqrt (normSq (w - b)) - (r + 15) - a := by
  filter_upwards [source_early_level_bounds,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ))]
    with t ht hm16
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
  have hslo := sourceRecordRadius_ge_terminal m hm.le ℓ (ν + 1) hdepth
  have hspos : 0 ≤ sourceRecordRadius m ℓ (ν + 1) := hm.le.trans hslo
  have he := mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le hspos
  rw [sourceRecordRadius_successor] at he
  change 2 * sourceRecordRadius m ℓ (ν + 1) ≤ r at he
  have hm16' : 16 ≤ m := hm16
  change 0 ≤ sourceRecordRadius m ℓ (ν + 1) - 14 ∧ _
  constructor
  · linarith
  constructor <;> change r / 2 ≤ _ <;> linarith

end SRWTightness
