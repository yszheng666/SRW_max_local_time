import SRWTightness.NaturalExponentialMoment
import SRWTightness.OccupationMoments

open MeasureTheory

namespace SRWTightness

 theorem integrable_domainLocalTime_pow (D : Finset Site) (x y : Site) (b : ℝ)
    (hb : 0 ≤ b) (hqb : (1 - 1 / killedGreen D y y) * b < 1) :
    Integrable (fun ω ↦ b ^ domainLocalTime D x y ω) pathLaw := by
  by_cases hy : y ∈ D
  · have hg1 := killedGreen_diag_ge_one D y hy
    have hgp : 0 < killedGreen D y y := lt_of_lt_of_le zero_lt_one hg1
    have hq0 : 0 ≤ 1 - 1 / killedGreen D y y := by
      apply sub_nonneg.mpr
      exact (div_le_one hgp).mpr hg1
    apply integrable_pow_of_nat_geometric_tail pathLaw _ (measurable_domainLocalTime D x y)
      (killedGreen D x y / killedGreen D y y) (1 - 1 / killedGreen D y y) b hq0 hb hqb
    intro n
    rw [occupation_probability_ge D x y hy (n + 1) (by omega)]
    simp
  · simp only [domainLocalTime_eq_zero_of_target_not_mem D x y hy, pow_zero]
    exact integrable_const 1

end SRWTightness
