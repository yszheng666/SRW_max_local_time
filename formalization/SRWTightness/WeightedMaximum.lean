import SRWTightness.MaximumPrinciple

namespace SRWTightness

 theorem abs_average_le (f : Direction → ℝ) :
    |(1 / 4 : ℝ) * ∑ d : Direction, f d| ≤ (1 / 4 : ℝ) * ∑ d : Direction, |f d| := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)

 theorem eq_zero_of_abs_subharmonic (D : Finset Site) (f : Site → ℝ)
    (hf : ∀ x, x ∉ D → f x = 0)
    (hh : ∀ x ∈ D, |f x| ≤ (1 / 4 : ℝ) * ∑ d : Direction, |f (x + step d)|) :
    f = 0 := by
  funext x
  have hle := finite_domain_comparison D (fun y ↦ |f y|) (fun _ ↦ 0) hh
    (by intro y hy; simp) (by intro y hy; simp [hf y hy]) x
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

 theorem weighted_harmonic_zero (D : Finset Site) (f : Site → ℝ)
    (hf : ∀ x, x ∉ D → f x = 0)
    (hh : ∀ x ∈ D, ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧
      f x = v * ((1 / 4 : ℝ) * ∑ d : Direction, f (x + step d))) : f = 0 := by
  apply eq_zero_of_abs_subharmonic D f hf
  intro x hx
  obtain ⟨v, hv0, hv1, he⟩ := hh x hx
  rw [he, abs_mul, abs_of_nonneg hv0]
  exact (mul_le_of_le_one_left (abs_nonneg _) hv1).trans (abs_average_le _)

end SRWTightness
