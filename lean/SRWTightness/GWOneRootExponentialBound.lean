import SRWTightness.ExternalGWOneRootMarginal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory

namespace SRWTightness

/-- The standard exact GW marginal implies the exponential weight used in the coarse endpoint sum. -/
theorem geometricGW_one_root_exponential_bound (hGW : GeometricGWOneRootMarginalInput)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} ≤
      Real.exp (1 - (k : ℝ) / ((j : ℝ) + 1)) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd : 0 < (j : ℝ) + 1 := by linarith
  have hd1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith
  have hr : 0 ≤ (j : ℝ) / ((j : ℝ) + 1) := div_nonneg hj0 hd.le
  have he : (j : ℝ) / ((j : ℝ) + 1) = 1 - 1 / ((j : ℝ) + 1) := by field_simp; ring
  have hex : (j : ℝ) / ((j : ℝ) + 1) ≤ Real.exp (-(1 / ((j : ℝ) + 1))) := by
    rw [he]
    linarith [Real.add_one_le_exp (-(1 / ((j : ℝ) + 1)))]
  have hp := pow_le_pow_left₀ hr hex (k - 1)
  have hc : 1 / ((j : ℝ) + 1) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hd)).mpr
    nlinarith
  have hi : 1 / ((j : ℝ) + 1) ≤ 1 := (div_le_one hd).mpr hd1
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  rw [hGW j k hj hk]
  calc
    _ ≤ ((j : ℝ) / ((j : ℝ) + 1)) ^ (k - 1) := by
      nlinarith [pow_nonneg hr (k - 1)]
    _ ≤ Real.exp (((k - 1 : ℕ) : ℝ) * (-(1 / ((j : ℝ) + 1)))) := by
      simpa only [Real.exp_nat_mul] using hp
    _ ≤ Real.exp (1 - (k : ℝ) / ((j : ℝ) + 1)) := by
      apply Real.exp_le_exp.mpr
      rw [hkcast]
      have hident : ((k : ℝ) - 1) * (-(1 / ((j : ℝ) + 1))) =
          -(k : ℝ) / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) := by ring
      rw [hident]
      simpa only [neg_div, add_comm, sub_eq_add_neg] using
        add_le_add_left hi (-(k : ℝ) / ((j : ℝ) + 1))

end SRWTightness
