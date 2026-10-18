import SRWTightness.DiskGreenFlatnessGap

namespace SRWTightness

/-- A gap of at least one eighth of the entrance radius gives the required inverse-radius error. -/
theorem green_gap_error_scale (C g r a A d : ℝ) (hC : 0 ≤ C) (hg : 0 ≤ g)
    (hr : 1 ≤ r) (ha : 0 ≤ a) (hA : A ≤ 2 * (a + 1)) (hd : r / 8 ≤ d) :
    C / d ^ 2 + g * (A / d) ≤ (64 * C + 16 * g) * (a + 1) / r := by
  have hr0 : 0 < r := by linarith
  have hd0 : 0 < d := by linarith
  have hsq : r ≤ 64 * d ^ 2 := by nlinarith
  have hc : C / d ^ 2 ≤ 64 * C / r := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd0) hr0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hC]
  have ha' : A / d ≤ 16 * (a + 1) / r := by
    apply (div_le_div_iff₀ hd0 hr0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hA hr0.le,
      mul_le_mul_of_nonneg_left (show r ≤ 8 * d by linarith) (show 0 ≤ a + 1 by linarith)]
  calc
    _ ≤ 64 * C / r + g * (16 * (a + 1) / r) :=
      add_le_add hc (mul_le_mul_of_nonneg_left ha' hg)
    _ = (64 * C + 16 * g * (a + 1)) / r := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hr0.le
      nlinarith [mul_nonneg hC ha]

/-- The intermediate radius 3a/2 leaves a uniform gap under the manuscript separation condition. -/
theorem source_intermediate_green_gap (r a : ℝ) (hr : 4 ≤ r) (hsep : 2 * a < r - 2) :
    r / 8 ≤ r - (3 * a / 2 + 2) := by linarith

/-- Uniform actual Green flatness on the intermediate comparison ball and its unit boundary. -/
theorem disk_green_intermediate_flatness (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (b x y : Site) (R r a : ℝ) (ha : 0 ≤ a) (hr : 4 ≤ r) (hsep : 2 * a < r - 2)
    (houter : r + 1 < R) (hlarge : R₀ ≤ r / 8)
    (hx : r - 1 ≤ Real.sqrt (normSq (x - b)) ∧ Real.sqrt (normSq (x - b)) ≤ r + 1)
    (hy : Real.sqrt (normSq (y - b)) ≤ 3 * a / 2 + 1) :
    |killedGreen (translateFinset b (diskFinset R)) x y -
        (2 / Real.pi) * (Real.log R - Real.log r)| ≤
      (128 * C + 32 * (2 / Real.pi)) * (a + 1) / r := by
  have hd := source_intermediate_green_gap r a hr hsep
  have hdR : r / 8 ≤ R - (3 * a / 2 + 2) := by linarith
  have hh := translated_disk_green_flatness_gap κ C R₀ hC hR₀ hbound b x y R r
    (3 * a / 2 + 1) (by linarith) houter (by linarith) (by linarith) hx hy
  have hg : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  have heR := green_gap_error_scale C (2 / Real.pi) r a (3 * a / 2 + 2)
    (R - (3 * a / 2 + 2)) hC hg (by linarith) ha (by linarith) hdR
  have her := green_gap_error_scale C (2 / Real.pi) r a (3 * a / 2 + 2)
    (r - (3 * a / 2 + 2)) hC hg (by linarith) ha (by linarith) hd
  have he : 3 * a / 2 + 1 + 1 = 3 * a / 2 + 2 := by ring
  rw [he] at hh
  calc
    _ ≤ _ := hh
    _ ≤ (64 * C + 16 * (2 / Real.pi)) * (a + 1) / r +
        (64 * C + 16 * (2 / Real.pi)) * (a + 1) / r := add_le_add heR her
    _ = _ := by ring

end SRWTightness
