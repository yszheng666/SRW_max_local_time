import SRWTightness.SourceEarlyLevelBounds
import SRWTightness.SourceEarlyPrefixContainment
import SRWTightness.SourceCommonPairDistanceChernoff

open Filter
namespace SRWTightness

/-- Both short-root balls and their exit sites lie inside the actual common observation ball.
Thus a mark retaining the ordered path through that ball retains complete short-root crossings. -/
theorem source_early_root_observation_geometry :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ), b ≠ w →
      1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      ∀ z ∈ ({b, w} : Finset Site),
      sourceEntranceDomain m 1 ℓ z ν ⊆ sourceExitDomain m 1 ℓ z ν ∧
      sourceExitDomain m 1 ℓ z ν ⊆ sourceCommonPairObservation b w ∧
      domainExitBoundary (sourceExitDomain m 1 ℓ z ν) ⊆
        (sourceCommonPairObservation b w : Set Site) := by
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
  have hm16' : 16 ≤ m := hm16
  have hfit₀ := shifted_domain_and_exit_inside b b (r + 14) (2 * ρ) (by linarith)
    (by simp only [sub_self, (normSq_eq_zero_iff 0).2 rfl, Real.sqrt_zero]; linarith)
  have hfit₁ := shifted_domain_and_exit_inside b w (r + 14) (2 * ρ) (by linarith)
    (by change ρ + (r + 14) + 1 < 2 * ρ; linarith)
  intro z hz
  have hnest := sourceEntranceDomain_subset_exit m 1 ℓ z ν (by norm_num)
    (by norm_num [sourceRecordBuffer]; exact hm16') hdepth
  refine ⟨hnest, ?_⟩
  have hdom : sourceExitDomain m 1 ℓ z ν = translateFinset z (diskFinset (r + 14)) := by
    norm_num [sourceExitDomain, sourceRecordBuffer, r]
  rw [hdom]
  change _ ⊆ translateFinset b (diskFinset (2 * ρ)) ∧ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hfit₀
  · exact hfit₁

end SRWTightness
