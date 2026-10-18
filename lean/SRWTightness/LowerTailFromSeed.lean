import SRWTightness.LowerTailAmplification
import SRWTightness.SpatialTargets
import Mathlib.Order.LiminfLimsup

open MeasureTheory Filter

namespace SRWTightness

theorem amplificationScale_half_lower (s : ℝ)
    (hs : 8 ≤ Real.exp (s * Real.sqrt Real.pi / 4)) :
    Real.exp (s * Real.sqrt Real.pi / 4) / 4 ≤ (amplificationScale s / 2 : ℕ) := by
  have hfloor := Nat.lt_floor_add_one (Real.exp (s * Real.sqrt Real.pi / 4))
  change Real.exp (s * Real.sqrt Real.pi / 4) < (amplificationScale s : ℝ) + 1 at hfloor
  have hj : (amplificationScale s : ℝ) ≤ 2 * (amplificationScale s / 2 : ℕ) + 1 := by
    exact_mod_cast (show amplificationScale s ≤ 2 * (amplificationScale s / 2) + 1 by omega)
  linarith

theorem seed_power_le_double_exp (s p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hs : 8 ≤ Real.exp (s * Real.sqrt Real.pi / 4)) :
    (1 - p) ^ (amplificationScale s / 2) ≤
      Real.exp (-(p / 4) * Real.exp (s * Real.sqrt Real.pi / 4)) := by
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - p)
    (Real.one_sub_le_exp_neg p) (amplificationScale s / 2)
  rw [← Real.exp_nat_mul] at hpow
  refine hpow.trans (Real.exp_le_exp.mpr ?_)
  have hj := amplificationScale_half_lower s hs
  nlinarith

/-- The double-exponential lower tail follows from the still-unproved spatial seed. -/
theorem disk_lower_tail_of_seed (h : DiskSeedClaim) :
    ∃ c s₀ : ℝ, 0 < c ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real {ω | diskFluctuation R ω < -s}) atTop ≤
        Real.exp (-c * Real.exp (Real.sqrt Real.pi * s / 4)) := by
  obtain ⟨p, hp, Rstar, hseed⟩ := h
  have hp1 : p ≤ 1 := (hseed Rstar le_rfl).trans measureReal_le_one
  refine ⟨p / 4, 32 / Real.sqrt Real.pi, by positivity, by positivity, ?_⟩
  intro s hs
  have hsq : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs0 : 0 ≤ s := (by positivity : (0 : ℝ) ≤ 32 / Real.sqrt Real.pi).trans hs
  have hex : 8 ≤ Real.exp (s * Real.sqrt Real.pi / 4) := by
    have hh := (div_le_iff₀ hsq).mp hs
    have he := Real.add_one_le_exp (s * Real.sqrt Real.pi / 4)
    linarith
  have hQ : (0 : ℝ) < amplificationScale s := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (amplificationScale_pos s hs0))
  have hr : Tendsto (fun R : ℝ ↦ R / amplificationScale s) atTop atTop :=
    tendsto_id.atTop_div_const hQ
  have hevent : ∀ᶠ R : ℝ in atTop,
      pathLaw.real {ω | diskFluctuation R ω < -s} ≤
        Real.exp (-(p / 4) * Real.exp (Real.sqrt Real.pi * s / 4)) := by
    filter_upwards [hr.eventually (eventually_ge_atTop Rstar),
      eventually_gt_atTop (amplificationScale s : ℝ)] with R hR hRQ
    have hb := (prob_disk_lower_shift_le_seed_power s R p hs0 hRQ (hseed _ hR)).trans
      (seed_power_le_double_exp s p hp.le hp1 hex)
    simpa only [mul_comm s (Real.sqrt Real.pi)] using hb
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun R ↦ measureReal_nonneg)) hevent

end SRWTightness
