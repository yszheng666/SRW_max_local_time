import SRWTightness.AnnulusLogEscapeBound
import SRWTightness.AnnulusEscapeIdentity

namespace SRWTightness

/-- Escape across the large annulus factors through escape across the double-radius annulus. -/
theorem annulusOuterExitProbability_product_upper (a R : ℝ) (ha : 4 ≤ a)
    (hRa : 2 * a ≤ R) (x : Site) (hx : normSq x ≤ (2 * a) ^ 2) :
    annulusOuterExitProbability a R x ≤
      (diskGreenEnergyConstant / ((2 / Real.pi) * Real.log (R / a))) *
        annulusOuterExitProbability a (2 * a) x := by
  let D := annulusFinset a (2 * a)
  let f : Site → ℝ := fun y ↦ 1 - setHitProbability (diskFinset R) (diskFinset a) y
  let M := diskGreenEnergyConstant / ((2 / Real.pi) * Real.log (R / a))
  have ha0 : 0 < a := by linarith
  have haR : a < R := by linarith
  have hsub : ∀ y ∈ diskFinset (2 * a), y ∈ diskFinset R := by
    intro y hy
    simp only [mem_diskFinset, disk, Set.mem_setOf_eq] at hy ⊢
    nlinarith
  have hh : f x = exitPayoff D f x := by
    apply harmonic_eq_exitPayoff
    intro y hy
    exact one_sub_setHitProbability_harmonic _ _ y
      (hsub y (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hy).2
  have hb : exitPayoff D f x ≤
      exitPayoff D (fun y ↦ 0 + M * (if y ∉ diskFinset (2 * a) then 1 else 0)) x := by
    apply exitPayoff_mono_on_exitRange
    intro y hy hyD
    by_cases hya : y ∈ diskFinset a
    · have hyR : y ∈ diskFinset R := by
        simp only [mem_diskFinset, disk, Set.mem_setOf_eq] at hya ⊢
        nlinarith
      have hy2 : y ∈ diskFinset (2 * a) := by
        simp only [mem_diskFinset, disk, Set.mem_setOf_eq] at hya ⊢
        nlinarith
      simp [f, setHitProbability_one _ _ y hyR hya, hy2]
    · have hy2 : y ∉ diskFinset (2 * a) := by
        intro h
        exact hyD (Finset.mem_sdiff.mpr ⟨h, hya⟩)
      have hlo : a ^ 2 ≤ normSq y := by
        simpa only [mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hya
      have hhi := annulusExitRange_normSq_upper a (2 * a) (by positivity) x hx y hy
      have hp := annulusOuterExitProbability_log_upper a R ha haR y hlo hhi
      rw [annulusOuterExitProbability_eq_one_sub_hit] at hp
      simpa [f, M, hy2] using hp
  rw [exitPayoff_affine, zero_add, exitPayoff_outside_eq_probability] at hb
  rw [annulusOuterExitProbability_eq_one_sub_hit]
  exact hh.le.trans hb

/-- One-step boundary escape has the product of inverse-radius and logarithmic decay. -/
theorem annulusOuterExitProbability_boundary_upper (a R : ℝ) (ha : 4 ≤ a)
    (hRa : 2 * a ≤ R) (x : Site) (hxlo : a ^ 2 ≤ normSq x)
    (hxhi : normSq x ≤ (a + 1) ^ 2) :
    annulusOuterExitProbability a R x ≤
      (diskGreenEnergyConstant / ((2 / Real.pi) * Real.log (R / a))) * (16 / (3 * a)) := by
  have ha0 : 0 < a := by linarith
  have hlog : 0 < Real.log (R / a) :=
    Real.log_pos ((one_lt_div ha0).mpr (by linarith))
  have hM : 0 ≤ diskGreenEnergyConstant / ((2 / Real.pi) * Real.log (R / a)) :=
    div_nonneg diskGreenEnergyConstant_pos.le (mul_nonneg (by positivity) hlog.le)
  exact (annulusOuterExitProbability_product_upper a R ha hRa x (by nlinarith)).trans
    (mul_le_mul_of_nonneg_left (annulusOuterExitProbability_near_upper a ha x hxlo hxhi) hM)

end SRWTightness
