import SRWTightness.AnnulusExitGeometry
import SRWTightness.ExitPayoffRangeComparison
import SRWTightness.PotentialRadiusComparison
import SRWTightness.PotentialKernelPoisson

namespace SRWTightness

/-- A true-walk annulus inequality using only the already proved coarse potential bounds. -/
theorem annulusOuterExitProbability_potential_bound (a R : ℝ) (ha : 4 ≤ a) (hRa : a ≤ R)
    (x : Site) (hx : a ^ 2 ≤ normSq x) :
    (2 / Real.pi) * (Real.log R - Real.log (a - 1)) * annulusOuterExitProbability a R x ≤
      potentialKernel x - ((2 / Real.pi) * Real.log (a - 1) - potentialLowerConstant) := by
  let D := annulusFinset a R
  let L := (2 / Real.pi) * Real.log (a - 1) - potentialLowerConstant
  let U := (2 / Real.pi) * Real.log R - potentialLowerConstant
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
  have hh := exitPayoff_mono_on_exitRange D
    (fun y ↦ L + (U - L) * (if y ∉ diskFinset R then 1 else 0)) potentialKernel x
    (fun y hy _ ↦ by
      by_cases hyR : y ∉ diskFinset R
      · simp only [if_pos hyR, mul_one, add_sub_cancel]
        apply potentialKernel_radius_lower y R (by linarith)
        simpa only [mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hyR
      · simp only [if_neg hyR, mul_zero, add_zero]
        exact potentialKernel_radius_lower y (a - 1) (by linarith)
          (annulusExitRange_normSq_lower a R (by linarith) x hx y hy))
  rw [exitPayoff_affine, exitPayoff_outside_eq_probability, ← hhar] at hh
  have hp : L + (U - L) * annulusOuterExitProbability a R x ≤ potentialKernel x := hh
  have he : U - L = (2 / Real.pi) * (Real.log R - Real.log (a - 1)) := by
    dsimp [U, L]
    ring
  rw [he] at hp
  dsimp [L] at hp
  linarith

end SRWTightness
