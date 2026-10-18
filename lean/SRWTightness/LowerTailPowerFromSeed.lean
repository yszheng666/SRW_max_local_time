import SRWTightness.LowerTailFromSeed

open MeasureTheory Filter

namespace SRWTightness

/-- The literal seed-power intermediate bound and double-exponential bound use the same seed. -/
theorem disk_lower_tail_power_of_seed (h : DiskSeedClaim) :
    ∃ p c s₀ : ℝ, 0 < p ∧ p ≤ 1 ∧ 0 < c ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real {ω | diskFluctuation R ω < -s}) atTop ≤
        (1 - p) ^ (amplificationScale s / 2) ∧
      (1 - p) ^ (amplificationScale s / 2) ≤
        Real.exp (-c * Real.exp (Real.sqrt Real.pi * s / 4)) := by
  obtain ⟨p, hp, Rstar, hseed⟩ := h
  have hp1 : p ≤ 1 := (hseed Rstar le_rfl).trans measureReal_le_one
  refine ⟨p, p / 4, 32 / Real.sqrt Real.pi, hp, hp1, by positivity, by positivity, ?_⟩
  intro s hs
  have hsq : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs0 : 0 ≤ s := (by positivity : (0 : ℝ) ≤ 32 / Real.sqrt Real.pi).trans hs
  have hex : 8 ≤ Real.exp (s * Real.sqrt Real.pi / 4) := by
    have hh := (div_le_iff₀ hsq).mp hs
    have he := Real.add_one_le_exp (s * Real.sqrt Real.pi / 4)
    linarith
  have hQ : (0 : ℝ) < amplificationScale s := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (amplificationScale_pos s hs0)
  have hr : Tendsto (fun R : ℝ ↦ R / amplificationScale s) atTop atTop :=
    tendsto_id.atTop_div_const hQ
  have hevent : ∀ᶠ R : ℝ in atTop,
      pathLaw.real {ω | diskFluctuation R ω < -s} ≤
        (1 - p) ^ (amplificationScale s / 2) := by
    filter_upwards [hr.eventually (eventually_ge_atTop Rstar),
      eventually_gt_atTop (amplificationScale s : ℝ)] with R hR hRQ
    exact prob_disk_lower_shift_le_seed_power s R p hs0 hRQ (hseed _ hR)
  refine ⟨limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (fun R ↦ measureReal_nonneg)) hevent, ?_⟩
  simpa only [mul_comm s (Real.sqrt Real.pi)] using
    seed_power_le_double_exp s p hp.le hp1 hex

end SRWTightness
