import SRWTightness.SourceEarlyDistanceGeometry

open Filter
namespace SRWTightness

/-- A strict radial margin puts a translated disk and all its one-step exits in another disk. -/
theorem shifted_domain_and_exit_inside (b w : Site) (r R : ℝ) (hr : 0 ≤ r)
    (hfit : Real.sqrt (normSq (w - b)) + r + 1 < R) :
    translateFinset w (diskFinset r) ⊆ translateFinset b (diskFinset R) ∧
      domainExitBoundary (translateFinset w (diskFinset r)) ⊆
        (translateFinset b (diskFinset R) : Set Site) := by
  have hd := Real.sqrt_nonneg (normSq (w - b))
  have hR : 0 < R := by linarith
  have hbound (y : Site) (hy : normSq (y - w) ≤ (r + 1) ^ 2) :
      y ∈ translateFinset b (diskFinset R) := by
    have hh := normSq_add_bound (w - b) (y - w) hd (by linarith : 0 ≤ r + 1)
      (le_of_eq (normSq_eq_sq_sqrt (w - b))) hy
    rw [show (w - b) + (y - w) = y - b by abel] at hh
    have hs : (Real.sqrt (normSq (w - b)) + (r + 1)) ^ 2 < R ^ 2 :=
      (sq_lt_sq₀ (by positivity) hR.le).mpr (by linarith)
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using
      hh.trans_lt hs
  constructor
  · intro y hy
    have hh : normSq (y - w) < r ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy
    exact hbound y (by nlinarith)
  · intro y hy
    have hh := (translated_disk_boundary_radial w r hr y hy).2
    have hn := Real.sqrt_nonneg (normSq (y - w))
    have hs := normSq_eq_sq_sqrt (y - w)
    exact hbound y (by nlinarith)

/-- The source early long balls, including their exit sites, lie inside the common entrance ball.
The deterministic invariance of the prefix under erasing or refilling is a separate obligation. -/
theorem source_early_prefix_containment (J₀ : ℕ) (hJ₀ : 3 ≤ J₀) :
    ∃ a₀ : ℕ, ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let K := sourceEntranceDomain m 1 ℓ b j
      C b ∪ C w ⊆ K ∧ domainExitBoundary (C b) ⊆ (K : Set Site) ∧
        domainExitBoundary (C w) ⊆ (K : Set Site) := by
  obtain ⟨a₀, hlevels⟩ := source_early_distance_levels J₀
  refine ⟨a₀, ?_⟩
  filter_upwards [hlevels, source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (14 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hlevels hN htime hm14 ht0
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := Real.sqrt (normSq (w - b))
  let r := sourceRecordRadius m ℓ (ν - J)
  let R := sourceCommonPairInnerRadius t j
  have hlev := hlevels a ha hrange
  have ha1 : 1 ≤ a := by have hp := hlev.1; omega
  have hJ : 3 ≤ J := by dsimp [J, sourceEarlyDistanceGap]; omega
  have hJa : J ≤ a := by have hp := hlev.1; change 0 < a - J at hp; omega
  have hj : j + J = a := Nat.sub_add_cancel hJa
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hlev.2.2]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hrad : m ≤ r := sourceRecordRadius_ge_terminal m (sourceLowerRadius_pos t).le ℓ _ (by omega)
  have hm : 14 ≤ m := hm14
  have hρ : 0 < ρ := by
    have hh := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    exact Real.sqrt_pos.2 (by linarith)
  have hr0 : 0 < sourceRecordRadius m ℓ 0 := by unfold sourceRecordRadius; positivity
  have hlog : 1 ≤ Real.log (sourceRecordRadius m ℓ 0 / ρ) :=
    (Nat.one_le_floor_iff _).mp ha1
  have houter : ρ ≤ sourceRecordRadius m ℓ 0 := by
    have he := Real.exp_le_exp.mpr (show 0 ≤ Real.log (sourceRecordRadius m ℓ 0 / ρ) by linarith)
    rw [Real.exp_zero, Real.exp_log (div_pos hr0 hρ)] at he
    exact (one_le_div hρ).mp he
  have hsmall : r < Real.exp (-4) * ρ := source_pair_long_radius t ρ hρ houter ν J rfl
  have he : Real.exp (-4) ≤ (1 / 5 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (a := (5 : ℝ)) (b := Real.exp 4)
        (by norm_num) (by linarith [Real.add_one_le_exp (4 : ℝ)]))
  have hrρ := hsmall.trans_le (mul_le_mul_of_nonneg_right he hρ.le)
  have hsep := (source_common_pair_log_separation t ρ hρ houter j J hj).1
  have hRpos : 0 < R := sourceCommonPairInnerRadius_pos t j
  have hlarge : Real.exp ((J : ℝ) - 1) * ρ ≤ R := by
    have hh := Real.exp_le_exp.mpr
      (show (J : ℝ) - 1 + Real.log ρ ≤ Real.log R by linarith)
    rwa [Real.exp_add, Real.exp_log hρ, Real.exp_log hRpos] at hh
  have hJreal : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  have he2 := Real.add_one_le_exp (2 : ℝ)
  have hexp := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ J - 1 by linarith)
  have hRρ : 3 * ρ ≤ R := by
    have hh := mul_le_mul_of_nonneg_right (show 3 ≤ Real.exp ((J : ℝ) - 1) by linarith) hρ.le
    linarith
  have hwfit := shifted_domain_and_exit_inside b w (r + 14) (R - 14)
    (by linarith) (by change ρ + (r + 14) + 1 < R - 14; linarith)
  have hbfit := shifted_domain_and_exit_inside b b (r + 14) (R - 14)
    (by linarith) (by simp only [sub_self, (normSq_eq_zero_iff 0).2 rfl, Real.sqrt_zero]; linarith)
  have hresult := And.intro (Finset.union_subset hbfit.1 hwfit.1) (And.intro hbfit.2 hwfit.2)
  simpa only [sourceExitDomain, sourceEntranceDomain, sourceRecordBuffer, mul_one,
    show (4 : ℝ) + 10 = 14 by norm_num, R, sourceCommonPairInnerRadius, r] using hresult

end SRWTightness
