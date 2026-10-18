import SRWTightness.PotentialRadialPerturbation

namespace SRWTightness

/-- The logarithmic radial error uses the actual positive gap, without a half-radius restriction. -/
theorem log_radius_gap_error (r R A : ℝ) (hA : 0 ≤ A) (hgap : 0 < R - A)
    (hlo : R - A ≤ r) (hhi : r ≤ R + A) :
    |Real.log r - Real.log R| ≤ A / (R - A) := by
  have hR : 0 < R := by linarith
  have hr : 0 < r := by linarith
  have hu := Real.log_le_sub_one_of_pos (div_pos hr hR)
  have hl := Real.log_le_sub_one_of_pos (div_pos hR hr)
  rw [Real.log_div hr.ne' hR.ne'] at hu
  rw [Real.log_div hR.ne' hr.ne'] at hl
  have hup : r / R - 1 ≤ A / (R - A) := by
    apply (le_div_iff₀ hgap).mpr
    apply (mul_le_mul_iff_right₀ hR).mp
    have he : R * ((r / R - 1) * (R - A)) = (r - R) * (R - A) := by
      field_simp
      <;> ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right (show r - R ≤ A by linarith) hgap.le]
  have hdown : R / r - 1 ≤ A / (R - A) := by
    apply (le_div_iff₀ hgap).mpr
    apply (mul_le_mul_iff_right₀ hr).mp
    have he : r * ((R / r - 1) * (R - A)) = (R - r) * (R - A) := by
      field_simp
      <;> ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right (show R - r ≤ A by linarith) hgap.le,
      mul_le_mul_of_nonneg_left hlo hA]
  exact abs_le.mpr ⟨by linarith [hl.trans hdown], hu.trans hup⟩

/-- Potential kernel radial control with only a positive separation gap. -/
theorem potential_kernel_radial_gap (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (R A : ℝ) (hA : 0 ≤ A) (hlarge : R₀ ≤ R - A) (z : Site)
    (hlo : R - A ≤ Real.sqrt (normSq z)) (hhi : Real.sqrt (normSq z) ≤ R + A) :
    |potentialKernel z - ((2 / Real.pi) * Real.log R + κ)| ≤
      C / (R - A) ^ 2 + (2 / Real.pi) * (A / (R - A)) := by
  have hgap : 0 < R - A := by linarith
  have hs := Real.sq_sqrt (normSq_nonneg z)
  have hn : (R - A) ^ 2 ≤ normSq z := by nlinarith
  have hn0 : 0 < normSq z := lt_of_lt_of_le (sq_pos_of_pos hgap) hn
  have hd : C / normSq z ≤ C / (R - A) ^ 2 := by
    apply (div_le_div_iff₀ hn0 (sq_pos_of_pos hgap)).mpr
    exact mul_le_mul_of_nonneg_left hn hC
  have hp := hbound z (hlarge.trans hlo)
  have hl := log_radius_gap_error (Real.sqrt (normSq z)) R A hA hgap hlo hhi
  have hg : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  calc
    _ = |(potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)) +
        (2 / Real.pi) * (Real.log (Real.sqrt (normSq z)) - Real.log R)| := by congr 1; ring
    _ ≤ |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| +
        |(2 / Real.pi) * (Real.log (Real.sqrt (normSq z)) - Real.log R)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hg]
      exact add_le_add (hp.trans hd) (mul_le_mul_of_nonneg_left hl hg)

end SRWTightness
