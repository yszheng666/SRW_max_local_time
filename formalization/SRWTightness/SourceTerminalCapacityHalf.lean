import SRWTightness.SourceReferenceIntensity
import SRWTightness.CapacityMonotone

namespace SRWTightness

/-- Logarithmic separation implies the actual source reference mass is at most one half. -/
theorem source_terminal_capacity_half (b : Site) (m H a : ℝ) (K : Finset Site)
    (ha : 1 ≤ a) (hma : 2 * a ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m)
    (hK : K ⊆ translateFinset b (diskFinset a))
    (hlog : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
      Real.log m - Real.log a) :
    sourceReferenceIntensity m H *
      capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 := by
  let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
  let L := translateFinset b (diskFinset a)
  have hm0 : 0 < m := by linarith
  have ha0 : 0 < a := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hR : m ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  have hLD : L ⊆ D :=
    Finset.image_subset_image (diskFinset_mono _ _ ha0.le (by linarith))
  have hne : L.Nonempty := Finset.Nonempty.image ⟨0, zero_mem_diskFinset a ha0⟩ _
  have hc := capacity_pos D L hLD hne
  have he := capacity_energy_source_bound b m a H ha hma (by
    rw [abs_of_nonneg hH]
    linarith)
  have hi : (4 : ℝ) ≤ 1 / ((2 / Real.pi) * capacity D L) := by
    have hh := (abs_le.mp he).1
    change -(diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4) ≤
      1 / ((2 / Real.pi) * capacity D L) - (Real.log m - Real.log a) at hh
    linarith
  have hprod : 4 * ((2 / Real.pi) * capacity D L) ≤ 1 :=
    (le_div_iff₀ (mul_pos hg hc)).mp hi
  have hα := sourceReferenceIntensity_bounds m H hm0 hH hHm
  have hmono := capacity_mono_set D K L hK hLD
  calc
    sourceReferenceIntensity m H * capacity D K ≤
        sourceReferenceIntensity m H * capacity D L := mul_le_mul_of_nonneg_left hmono hα.1.le
    _ ≤ (2 * (2 / Real.pi)) * capacity D L := mul_le_mul_of_nonneg_right hα.2 hc.le
    _ ≤ 1 / 2 := by nlinarith

end SRWTightness
