import SRWTightness.EntropyScalarBound
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace SRWTightness

/-- A probability density has L1 distance at most twice the square root of its relative entropy. -/
theorem density_entropy_l1_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hnon : ∀ ω, 0 ≤ f ω) (hmass : ∫ ω, f ω ∂μ = 1)
    (hlog : Integrable (fun ω ↦ f ω * Real.log (f ω)) μ) :
    (∫ ω, |f ω - 1| ∂μ) ^ 2 ≤ 4 * ∫ ω, f ω * Real.log (f ω) ∂μ ∧
    (∫ ω, |f ω - 1| ∂μ) ≤ 2 * Real.sqrt (∫ ω, f ω * Real.log (f ω) ∂μ) := by
  let H := fun ω ↦ f ω * Real.log (f ω) - f ω + 1
  have hH : Integrable H μ := (hlog.sub hf).add (integrable_const 1)
  have hHnon (ω : Ω) : 0 ≤ H ω := entropy_integrand_nonnegative (f ω) (hnon ω)
  have hHmean : ∫ ω, H ω ∂μ = ∫ ω, f ω * Real.log (f ω) ∂μ := by
    dsimp only [H]
    have hsub : Integrable (fun ω ↦ f ω * Real.log (f ω) - f ω) μ := hlog.sub hf
    rw [integral_add hsub (integrable_const (1 : ℝ)), integral_sub hlog hf, hmass]
    simp
  have habs : Integrable (fun ω ↦ |f ω - 1|) μ := (hf.sub (integrable_const 1)).abs
  have hplus : Integrable (fun ω ↦ f ω + 1) μ := hf.add (integrable_const 1)
  have hplusmean : ∫ ω, (f ω + 1) ∂μ = 2 := by
    rw [integral_add hf (integrable_const 1), hmass]
    norm_num
  have hp (q : ℝ) (hq : 0 ≤ q) :
      2 * q * (∫ ω, |f ω - 1| ∂μ) ≤
        (∫ ω, f ω * Real.log (f ω) ∂μ) + 4 * q ^ 2 := by
    have hh := integral_mono (habs.const_mul (2 * q))
      (hH.add (hplus.const_mul (2 * q ^ 2)))
      (fun ω ↦ entropy_absolute_error_parameter (f ω) q (hnon ω) hq)
    change (∫ ω, 2 * q * |f ω - 1| ∂μ) ≤
      ∫ ω, H ω + 2 * q ^ 2 * (f ω + 1) ∂μ at hh
    rw [integral_const_mul, integral_add hH (hplus.const_mul (2 * q ^ 2)),
      integral_const_mul, hHmean, hplusmean] at hh
    nlinarith
  have hL : 0 ≤ ∫ ω, |f ω - 1| ∂μ := integral_nonneg (fun ω ↦ abs_nonneg _)
  have hK : 0 ≤ ∫ ω, f ω * Real.log (f ω) ∂μ := by
    rw [← hHmean]
    exact integral_nonneg hHnon
  have hs : (∫ ω, |f ω - 1| ∂μ) ^ 2 ≤ 4 * ∫ ω, f ω * Real.log (f ω) ∂μ := by
    have hh := hp ((∫ ω, |f ω - 1| ∂μ) / 4) (by positivity)
    nlinarith
  refine ⟨hs, ?_⟩
  have hr := Real.sq_sqrt hK
  nlinarith [Real.sqrt_nonneg (∫ ω, f ω * Real.log (f ω) ∂μ)]

end SRWTightness
