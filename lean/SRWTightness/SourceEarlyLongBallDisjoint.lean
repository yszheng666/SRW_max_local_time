import SRWTightness.SourceExteriorGeometry

open Filter
namespace SRWTightness

/-- Open translated disks are disjoint when their radii sum to at most the center distance. -/
theorem translated_disks_disjoint (b w : Site) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hgap : r + s ≤ Real.sqrt (normSq (w - b))) :
    Disjoint (translateFinset b (diskFinset r)) (translateFinset w (diskFinset s)) := by
  apply Finset.disjoint_left.mpr
  intro y hy hw
  have hyr : normSq (y - b) < r ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy
  have hyw : normSq (w - y) < s ^ 2 := by
    have hh : normSq (y - w) < s ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hw
    simpa only [show w - y = -(y - w) by abel, normSq_neg] using hh
  have hsum := normSq_add_lt_of_le_of_lt (y - b) (w - y) hr hs hyr.le hyw
  rw [show (y - b) + (w - y) = w - b by abel] at hsum
  have hd := normSq_eq_sq_sqrt (w - b)
  nlinarith

/-- The actual early long balls are disjoint, including the fixed boundary buffers. -/
theorem source_early_long_balls_disjoint :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ), b ≠ w →
      1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      Disjoint (sourceExitDomain m 1 ℓ b (ν - J)) (sourceExitDomain m 1 ℓ w (ν - J)) := by
  filter_upwards [source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (14 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hN htime hm14 ht0
  intro b w ν J hbw ha hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := Real.sqrt (normSq (w - b))
  let r := sourceRecordRadius m ℓ (ν - J)
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hνℓ : ν - J ≤ ℓ := by omega
  have hrad : m ≤ r := sourceRecordRadius_ge_terminal m (sourceLowerRadius_pos t).le ℓ _ hνℓ
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
  have hsmall : r < Real.exp (-4) * ρ := source_pair_long_radius t ρ hρ houter ν J hform
  have he : Real.exp (-4) ≤ (1 / 5 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (a := (5 : ℝ)) (b := Real.exp 4)
        (by norm_num) (by linarith [Real.add_one_le_exp (4 : ℝ)]))
  have hbound := hsmall.trans_le (mul_le_mul_of_nonneg_right he hρ.le)
  have hm : 14 ≤ m := hm14
  have hh := translated_disks_disjoint b w (r + 14) (r + 14) (by linarith)
    (by linarith) (by change r + 14 + (r + 14) ≤ ρ; linarith)
  simpa only [sourceExitDomain, sourceRecordBuffer, mul_one,
    show (4 : ℝ) + 10 = 14 by norm_num] using hh

end SRWTightness
