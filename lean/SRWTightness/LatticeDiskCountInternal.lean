import SRWTightness.LatticeIntegerBoxCount
import SRWTightness.LatticePairCount

namespace SRWTightness

/-- The uniform lattice disk count follows internally from its enclosing integer box. -/
theorem lattice_disk_count_input_internal : LatticeDiskCountInput := by
  refine ⟨25, by norm_num, ?_⟩
  intro r hr
  let B : ℤ := ⌈r⌉
  have hceil : r ≤ (B : ℝ) := Int.le_ceil r
  have hB : 0 ≤ B := by
    have hreal : (0 : ℝ) ≤ (B : ℝ) := by linarith
    exact_mod_cast hreal
  have htop : (B : ℝ) ≤ 2 * r := by
    have hh := Int.ceil_lt_add_one r
    change (B : ℝ) < r + 1 at hh
    linarith
  have hc : ((diskFinset r).card : ℝ) ≤
      (((Finset.Icc (-B) B).product (Finset.Icc (-B) B)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (diskFinset_subset_integer_box r (by linarith) B hceil)
  rw [lattice_integer_box_card B hB] at hc
  have hspan : 0 ≤ 2 * (B : ℝ) + 1 := by exact_mod_cast (by omega : 0 ≤ 2 * B + 1)
  have hbound : 2 * (B : ℝ) + 1 ≤ 5 * r := by linarith
  have hsq := mul_self_le_mul_self hspan hbound
  nlinarith

end SRWTightness
