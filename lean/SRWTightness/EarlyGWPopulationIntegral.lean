import SRWTightness.EarlyGWPopulationSum
import SRWTightness.CommonGWEndpointIntegral

open MeasureTheory
open scoped BigOperators ENNReal

namespace SRWTightness

/-- The endpoint population sum bounds the full nonnegative GW integral under a height cap. -/
theorem early_gw_population_lintegral (hGW : GeometricGWOneRootMarginalInput)
    (j : ℕ) (hj : 1 ≤ j) (b e : ℝ) (hb : 0 < b) (hbd : b ≤ 4 * ((j : ℝ) + 1))
    (s : Set GeometricGWRecord) (hs : ∀ r ∈ s, geometricGWHeight r j ≤ b) :
    (∫⁻ r in s, ENNReal.ofReal (Real.exp
      (2 * b + 4 * (geometricGWPopulation r j : ℝ) / b + e)) ∂geometricGWRecordLaw 1 j) ≤
      ENNReal.ofReal (36 * (j : ℝ) ^ 2 *
        Real.exp (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) + e)) := by
  have hh := common_gw_endpoint_integral_upper j b hb.le s hs
    (fun k ↦ ENNReal.ofReal (Real.exp (2 * b + 4 * (k : ℝ) / b + e)))
  have hsum := ENNReal.ofReal_le_ofReal (early_gw_population_sum hGW j hj b e hb hbd)
  rw [ENNReal.ofReal_sum_of_nonneg (by intro k hk; positivity)] at hsum
  apply hh.trans
  have heq : (∑ k ∈ Finset.range (⌊b ^ 2 / 2⌋₊ + 1),
      ENNReal.ofReal (Real.exp (2 * b + 4 * (k : ℝ) / b + e)) *
        (geometricGWRecordLaw 1 j) {r | geometricGWPopulation r j = k}) =
      ∑ k ∈ Finset.range (⌊b ^ 2 / 2⌋₊ + 1), ENNReal.ofReal
        ((geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
          Real.exp (2 * b + 4 * (k : ℝ) / b + e)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [ENNReal.ofReal_mul measureReal_nonneg,
      ofReal_measureReal (measure_ne_top _ _)]
    exact mul_comm _ _
  rw [heq]
  exact hsum

end SRWTightness
