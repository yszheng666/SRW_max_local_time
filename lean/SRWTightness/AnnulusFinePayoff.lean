import SRWTightness.AnnulusFineBoundary
import SRWTightness.ExitPayoffRangeComparison
import SRWTightness.PotentialKernelPoisson

namespace SRWTightness

/-- Boundary asymptotics pass to the exact SRW annulus exit probability. -/
theorem annulus_potential_exit_approximation (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (a R : ℝ) (ha : 2 ≤ a) (ha₀ : R₀ + 1 ≤ a) (haR : a ≤ R)
    (x : Site) (hxl : a ^ 2 ≤ normSq x) (hxu : normSq x ≤ R ^ 2) :
    |potentialKernel x - ((2 / Real.pi) * Real.log a + κ +
      ((2 / Real.pi) * (Real.log R - Real.log a)) * annulusOuterExitProbability a R x)| ≤
      (4 * C + 2 * (2 / Real.pi)) / a := by
  let D := annulusFinset a R
  let f : Site → ℝ := fun y ↦ (2 / Real.pi) * Real.log a + κ +
    ((2 / Real.pi) * (Real.log R - Real.log a)) * (if y ∉ diskFinset R then 1 else 0)
  let e := (4 * C + 2 * (2 / Real.pi)) / a
  have hhar : potentialKernel x = exitPayoff D potentialKernel x := by
    apply harmonic_eq_exitPayoff
    intro y hy
    have hysq := ((mem_annulusFinset a R y).mp hy).2
    have hy0 : y ≠ 0 := by
      intro he
      rw [he] at hysq
      simp only [normSq, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_add] at hysq
      nlinarith
    have he := potentialKernel_poisson y
    rw [if_neg hy0] at he
    linarith
  have hb : ∀ y ∈ domainExitRange D x, y ∉ D → |potentialKernel y - f y| ≤ e := by
    intro y hy hyD
    exact annulus_exit_potential_error κ C R₀ hC hR₀ hbound a R ha ha₀ haR x hxl hxu y hy hyD
  have hlo := exitPayoff_mono_on_exitRange D (fun y ↦ -e + 1 * f y) potentialKernel x
    (fun y hy hyD ↦ by have hh := (abs_le.mp (hb y hy hyD)).1; linarith)
  have hhi := exitPayoff_mono_on_exitRange D potentialKernel (fun y ↦ e + 1 * f y) x
    (fun y hy hyD ↦ by have hh := (abs_le.mp (hb y hy hyD)).2; linarith)
  rw [exitPayoff_affine, ← hhar, one_mul] at hlo hhi
  have hf : exitPayoff D f x = (2 / Real.pi) * Real.log a + κ +
      ((2 / Real.pi) * (Real.log R - Real.log a)) * annulusOuterExitProbability a R x := by
    dsimp only [f, D]
    rw [exitPayoff_affine, exitPayoff_outside_eq_probability]
    rfl
  rw [hf] at hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SRWTightness
