import SRWTightness.EarlyPopulationEndpoint

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- The finite weighted GW population sum, including zero, is bounded at the barrier endpoint. -/
theorem early_gw_population_sum (hGW : GeometricGWOneRootMarginalInput)
    (j : ℕ) (hj : 1 ≤ j) (b e : ℝ) (hb : 0 < b) (hbd : b ≤ 4 * ((j : ℝ) + 1)) :
    (∑ k ∈ Finset.range (⌊b ^ 2 / 2⌋₊ + 1),
      (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
        Real.exp (2 * b + 4 * (k : ℝ) / b + e)) ≤
      36 * (j : ℝ) ^ 2 * Real.exp (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) + e) := by
  let N := ⌊b ^ 2 / 2⌋₊
  let V := Real.exp (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) + e)
  have hd : 0 < (j : ℝ) + 1 := by positivity
  have hfloor : (N : ℝ) ≤ b ^ 2 / 2 := Nat.floor_le (by positivity)
  have hterm (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
      (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
        Real.exp (2 * b + 4 * (k : ℝ) / b + e) ≤ V := by
    have hkn : k ≤ N := by have hh := Finset.mem_range.mp hk; omega
    apply early_population_weight_endpoint b ((j : ℝ) + 1) k e _ hb hd hbd
      ((Nat.cast_le.mpr hkn).trans hfloor)
    by_cases hk0 : k = 0
    · subst k
      simpa using (measureReal_le_one (μ := geometricGWRecordLaw 1 j)
        (s := {r | geometricGWPopulation r j = 0}))
    · exact source_gw_one_root_exponential_bound hGW j k hj (by omega)
  have hsum := Finset.sum_le_sum hterm
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hsquare : b ^ 2 ≤ 16 * ((j : ℝ) + 1) ^ 2 := by
    nlinarith only [pow_le_pow_left₀ hb.le hbd 2]
  have hN : ((N + 1 : ℕ) : ℝ) ≤ 36 * (j : ℝ) ^ 2 := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith [sq_nonneg ((j : ℝ) - 1)]
  calc
    _ ≤ ∑ _k ∈ Finset.range (N + 1), V := hsum
    _ = ((N + 1 : ℕ) : ℝ) * V := by simp
    _ ≤ 36 * (j : ℝ) ^ 2 * V := mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le

end SRWTightness
