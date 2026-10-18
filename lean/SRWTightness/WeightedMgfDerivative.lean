import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Tilted

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Integration against a nonnegative real density, including nonintegrable integrands. -/
theorem integral_nonnegative_density {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Ω → ℝ) (hH : Measurable H) (hH0 : ∀ ω, 0 ≤ H ω) (f : Ω → ℝ) :
    (∫ ω, f ω ∂μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω))) = ∫ ω, H ω * f ω ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun ω ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hH0 _), smul_eq_mul]

/-- Integrability under a nonnegative real density. -/
theorem integrable_nonnegative_density_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Ω → ℝ) (hH : Measurable H) (hH0 : ∀ ω, 0 ≤ H ω) (f : Ω → ℝ) :
    Integrable f (μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω))) ↔
      Integrable (fun ω ↦ H ω * f ω) μ := by
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun ω ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hH0 _), smul_eq_mul]

/-- Differentiation of an exponentially weighted nonnegative observation. -/
theorem hasDerivAt_weighted_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H X : Ω → ℝ) (hH : Measurable H) (hH0 : ∀ ω, 0 ≤ H ω)
    (t : ℝ) (ht : t ∈ interior (integrableExpSet X
      (μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω))))) :
    HasDerivAt (fun s ↦ ∫ ω, H ω * Real.exp (s * X ω) ∂μ)
      (∫ ω, H ω * (X ω * Real.exp (t * X ω)) ∂μ) t := by
  have hd := hasDerivAt_mgf ht
  change HasDerivAt
    (fun s ↦ ∫ ω, Real.exp (s * X ω) ∂μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω)))
    (∫ ω, X ω * Real.exp (t * X ω) ∂μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω))) t at hd
  simp only [integral_nonnegative_density μ H hH hH0] at hd
  exact hd

/-- An L2 density keeps a point in the exponential domain when the doubled tilt is interior. -/
theorem weighted_exponential_interior {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H X : Ω → ℝ) (hH : Measurable H) (hH0 : ∀ ω, 0 ≤ H ω)
    (hH2 : MemLp H 2 μ) (hX : Measurable X) (t : ℝ)
    (ht : t ∈ interior (integrableExpSet (fun ω ↦ 2 * X ω) μ)) :
    t ∈ interior (integrableExpSet X (μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω)))) := by
  apply interior_mono (s := integrableExpSet (fun ω ↦ 2 * X ω) μ) _ ht
  intro s hs
  apply (integrable_nonnegative_density_iff μ H hH hH0 _).mpr
  have hE : MemLp (fun ω ↦ Real.exp (s * X ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    have he : (fun ω ↦ Real.exp (s * X ω) ^ 2) =
        (fun ω ↦ Real.exp (s * (2 * X ω))) := by
      funext ω
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    exact hs
  exact hH2.integrable_mul hE

end SRWTightness
