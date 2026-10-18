import SRWTightness.LatticeAnnulusRectangle
import SRWTightness.LatticeDiskCountInternal

open Filter
namespace SRWTightness

/-- The full closed candidate annulus has a uniform quadratic lower bound. -/
theorem source_annulus_card_lower_internal (R : ℝ) (hR : 100 ≤ R) :
    (1 / 10000 : ℝ) * R ^ 2 ≤ ((sourceCandidateAnnulus R).card : ℝ) := by
  have hc : (⌊R / 100⌋₊ + 1) ^ 2 ≤ (sourceCandidateAnnulus R).card := by
    rw [← lattice_shifted_integer_rectangle_card ⌈R / 4⌉ ⌊R / 100⌋₊]
    exact Finset.card_le_card (source_annulus_integer_rectangle_subset R hR)
  have hcr : ((⌊R / 100⌋₊ : ℝ) + 1) ^ 2 ≤ ((sourceCandidateAnnulus R).card : ℝ) := by
    exact_mod_cast hc
  have hn := Nat.lt_floor_add_one (R / 100)
  have hs := mul_self_le_mul_self (by linarith : 0 ≤ R / 100) hn.le
  nlinarith

/-- Both quadratic bounds for the manuscript's entire candidate annulus are internally proved. -/
theorem lattice_annulus_count_input_internal : LatticeAnnulusCountInput := by
  obtain ⟨C, hC, hcount⟩ := lattice_disk_count_input_internal
  refine ⟨1 / 10000, 4 * C, by norm_num, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (100 : ℝ)] with R hR
  refine ⟨source_annulus_card_lower_internal R hR, ?_⟩
  have hR0 : 0 < R := by linarith
  have hc : (sourceCandidateAnnulus R).card ≤ (diskFinset (|R| + 1)).card := by
    apply Finset.card_le_card
    classical
    unfold sourceCandidateAnnulus
    exact Finset.filter_subset _ _
  have hcr : ((sourceCandidateAnnulus R).card : ℝ) ≤ (diskFinset (R + 1)).card := by
    rw [abs_of_pos hR0] at hc
    exact_mod_cast hc
  have hd := hcount (R + 1) (by linarith)
  have hs := mul_self_le_mul_self (by linarith : 0 ≤ R + 1)
    (by linarith : R + 1 ≤ 2 * R)
  calc
    _ ≤ ((diskFinset (R + 1)).card : ℝ) := hcr
    _ ≤ C * (R + 1) ^ 2 := hd
    _ ≤ 4 * C * R ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hs hC.le]

end SRWTightness
