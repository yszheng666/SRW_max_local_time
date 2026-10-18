import SRWTightness.LatticeClosedDiskCount
import SRWTightness.SourceUpperSpatialLogBounds

namespace SRWTightness

/-- Two spatial regions control the logarithmic hitting prefactor throughout the near-origin disk. -/
theorem source_upper_near_origin_log_sum (t : ℝ) (ht : 2 ≤ t)
    (hr : 1 ≤ Real.exp t / t ^ 2) (Z : Finset Site)
    (hZ : ∀ x ∈ Z, Real.sqrt (normSq x) ≤ Real.exp t / t) :
    (∑ x ∈ Z, (1 + Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1))) ≤
      101 * (Real.exp t / t) ^ 2 * (1 + 2 * Real.log t) +
        101 * (Real.exp t / t ^ 2) ^ 2 * (1 + t) := by
  classical
  have ht0 : 0 < t := by linarith
  have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hrr : Real.exp t / t ^ 2 ≤ Real.exp t / t :=
    div_le_div_of_nonneg_left (Real.exp_nonneg _) ht0 (by nlinarith)
  let I := Z.filter (fun x ↦ Real.sqrt (normSq x) < Real.exp t / t ^ 2)
  have hcard := lattice_closed_disk_count (Real.exp t / t) (hr.trans hrr) Z hZ
  have hinner : (I.card : ℝ) ≤ 101 * (Real.exp t / t ^ 2) ^ 2 :=
    lattice_closed_disk_count _ hr I (fun x hx ↦ (Finset.mem_filter.mp hx).2.le)
  have hpoint (x : Site) :
      1 + Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1) ≤
        (1 + 2 * Real.log t) +
          if Real.sqrt (normSq x) < Real.exp t / t ^ 2 then 1 + t else 0 := by
    split_ifs with hx
    · have hh := source_upper_spatial_log_global t x
      linarith
    · have hh := source_upper_spatial_log_outer t x ht0 (le_of_not_gt hx)
      linarith
  calc
    _ ≤ ∑ x ∈ Z, ((1 + 2 * Real.log t) +
        if Real.sqrt (normSq x) < Real.exp t / t ^ 2 then 1 + t else 0) :=
      Finset.sum_le_sum (fun x _ ↦ hpoint x)
    _ = (Z.card : ℝ) * (1 + 2 * Real.log t) + (I.card : ℝ) * (1 + t) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [I]
      <;> ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right hcard (by positivity))
      (mul_le_mul_of_nonneg_right hinner (by positivity))

end SRWTightness
