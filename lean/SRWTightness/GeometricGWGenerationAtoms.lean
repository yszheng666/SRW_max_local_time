import SRWTightness.NatAdditionLawAtoms
import SRWTightness.GeometricGWOneGeneration
import Mathlib.Data.Nat.Choose.Sum

open MeasureTheory

namespace SRWTightness

/-- Every positive-parent geometric generation has its exact negative-binomial atom. -/
theorem geometric_gw_generation_positive_parents_atom (k m : ℕ) :
    (geometricGWGenerationLaw (k + 1)).real {m} =
      ((m + k).choose m : ℝ) * (1 / 2 : ℝ) ^ (m + k + 1) := by
  induction k generalizing m with
  | zero =>
    rw [geometric_gw_generation_one, geometricGWOffspringLaw_singleton]
    simp
  | succ k ih =>
    rw [geometric_gw_generation_cons_atom]
    simp_rw [ih]
    have hsum : (∑ i ∈ Finset.range (m + 1), ((m - i + k).choose (m - i) : ℝ)) =
        ((m + k + 1).choose (k + 1) : ℝ) := by
      simp_rw [Nat.choose_symm_add]
      have hn : (∑ i ∈ Finset.range (m + 1), (m - i + k).choose k) =
          (m + k + 1).choose (k + 1) := by
        calc
          _ = ∑ i ∈ Finset.range (m + 1), (i + k).choose k := by
            simpa only [Nat.add_sub_cancel] using
              Finset.sum_range_reflect (fun i ↦ (i + k).choose k) (m + 1)
          _ = _ := Nat.sum_range_add_choose m k
      exact_mod_cast hn
    calc
      _ = (∑ i ∈ Finset.range (m + 1), ((m - i + k).choose (m - i) : ℝ)) *
          (1 / 2 : ℝ) ^ (m + k + 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        have him : i ≤ m := by have hh := Finset.mem_range.mp hi; omega
        have he : i + 1 + (m - i + k + 1) = m + k + 2 := by omega
        calc
          _ = ((m - i + k).choose (m - i) : ℝ) *
              ((1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ (m - i + k + 1)) := by ring
          _ = _ := by rw [← pow_add, he]
      _ = _ := by
        rw [hsum]
        have hc : (m + k + 1).choose (k + 1) = (m + (k + 1)).choose m := by
          simpa only [Nat.add_assoc] using
            (Nat.choose_symm_add (a := m) (b := k + 1)).symm
        rw [hc]
        congr 1 <;> omega

end SRWTightness
