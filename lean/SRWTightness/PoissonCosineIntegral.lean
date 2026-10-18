import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Tactic

open MeasureTheory InnerProductSpace
namespace SRWTightness

/-- The real Poisson kernel on the unit circle has total mass two pi. -/
theorem poisson_cosine_integral (r : ℝ) (hr : |r| < 1) :
    (∫ t in 0..2 * Real.pi,
      (1 - r ^ 2) / (1 + r ^ 2 - 2 * r * Real.cos t)) = 2 * Real.pi := by
  have hw : (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hr
  have hf : HarmonicOnNhd (fun _ : ℂ ↦ (1 : ℝ)) (Metric.closedBall (0 : ℂ) 1) :=
    harmonicOnNhd_const 1
  have h := hf.circleAverage_poissonKernel_smul hw
  have hp (t : ℝ) : poissonKernel 0 (r : ℂ) (circleMap 0 1 t) =
      (1 - r ^ 2) / (1 + r ^ 2 - 2 * r * Real.cos t) := by
    have hd : ‖circleMap 0 1 t - (r : ℂ)‖ ^ 2 =
        1 + r ^ 2 - 2 * r * Real.cos t := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      simp [Complex.normSq_eq_norm_sq, norm_circleMap_zero, Complex.mul_re,
        circleMap_zero_re]
      <;> ring
    simp only [poissonKernel_def, sub_zero, norm_circleMap_zero, abs_one,
      one_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hd]
  rw [Real.circleAverage_def] at h
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_one] at h
  simp_rw [hp] at h
  have hdiv : (∫ t in 0..2 * Real.pi,
      (1 - r ^ 2) / (1 + r ^ 2 - 2 * r * Real.cos t)) / (2 * Real.pi) = 1 := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  have he := (div_eq_iff (by positivity : 2 * Real.pi ≠ 0)).mp hdiv
  simpa only [one_mul] using he

end SRWTightness
