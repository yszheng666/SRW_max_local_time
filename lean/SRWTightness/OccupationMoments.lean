import SRWTightness.NaturalSecondMoment
import SRWTightness.TailGeometric
import SRWTightness.SetHitting

open MeasureTheory

namespace SRWTightness

 theorem domainLocalTime_eq_zero_of_target_not_mem (D : Finset Site) (x y : Site)
    (hy : y ∉ D) (ω : Sample) : domainLocalTime D x y ω = 0 := by
  by_contra h
  have hp : 0 < localTime ω (domainSteps D x ω) (y - x) := by
    change 0 < domainLocalTime D x y ω
    omega
  obtain ⟨i, hi, he⟩ := (localTime_pos_iff ω _ _).mp hp
  have hout : x + position ω i ∉ D := by
    have hh : x + position ω i = y := by rw [he]; abel
    rwa [hh]
  have ht : domainExit D x ω ≤ i := (domainExit_le_iff D x ω i).mpr ⟨i, le_rfl, hout⟩
  have hf : domainExit D x ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top ht
  rw [← coe_domainSteps D x ω hf] at ht
  have hh : domainSteps D x ω ≤ i := WithTop.coe_le_coe.mp ht
  omega

 theorem integrable_domainLocalTime_sq (D : Finset Site) (x y : Site) :
    Integrable (fun ω ↦ (domainLocalTime D x y ω : ℝ) ^ 2) pathLaw := by
  by_cases hy : y ∈ D
  · have hg1 := killedGreen_diag_ge_one D y hy
    have hgp : 0 < killedGreen D y y := lt_of_lt_of_le zero_lt_one hg1
    have hq0 : 0 ≤ 1 - 1 / killedGreen D y y := by
      apply sub_nonneg.mpr
      exact (div_le_one hgp).mpr hg1
    have hq1 : 1 - 1 / killedGreen D y y < 1 := by
      linarith [one_div_pos.mpr hgp]
    apply integrable_sq_of_nat_geometric_tail pathLaw _ (measurable_domainLocalTime D x y)
      (killedGreen D x y / killedGreen D y y) (1 - 1 / killedGreen D y y) hq0 hq1
    intro n
    rw [occupation_probability_ge D x y hy (n + 1) (by omega)]
    simp
  · simp only [domainLocalTime_eq_zero_of_target_not_mem D x y hy, Nat.cast_zero, zero_pow (by omega : 2 ≠ 0)]
    exact integrable_const 0

 theorem integrable_domainLocalTime_mul (D : Finset Site) (x y z : Site) :
    Integrable (fun ω ↦ (domainLocalTime D x y ω : ℝ) * domainLocalTime D x z ω) pathLaw := by
  have hi := (integrable_domainLocalTime_sq D x y).add (integrable_domainLocalTime_sq D x z)
  apply hi.mono'
    ((((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_domainLocalTime D x y)).mul
      ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_domainLocalTime D x z))).aestronglyMeasurable)
  filter_upwards [] with ω
  have ha : 0 ≤ (domainLocalTime D x y ω : ℝ) := Nat.cast_nonneg _
  have hb : 0 ≤ (domainLocalTime D x z ω : ℝ) := Nat.cast_nonneg _
  change ‖(domainLocalTime D x y ω : ℝ) * domainLocalTime D x z ω‖ ≤
    (domainLocalTime D x y ω : ℝ) ^ 2 + (domainLocalTime D x z ω : ℝ) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha hb)]
  nlinarith [sq_nonneg ((domainLocalTime D x y ω : ℝ) - domainLocalTime D x z ω)]

end SRWTightness
