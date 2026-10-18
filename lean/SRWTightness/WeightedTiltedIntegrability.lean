import SRWTightness.WeightedMgfDerivative

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace SRWTightness

/-- A weighted exponential neighborhood supplies every mixed polynomial moment under the tilt. -/
theorem weighted_tilted_pow_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H X : Ω → ℝ) (hH : Measurable H) (hH0 : ∀ ω, 0 ≤ H ω)
    (t : ℝ) (ht : t ∈ interior (integrableExpSet X μ))
    (htH : t ∈ interior (integrableExpSet X
      (μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω))))) (n : ℕ) :
    Integrable (fun ω ↦ H ω * X ω ^ n) (μ.tilted (fun ω ↦ t * X ω)) := by
  have hi := interior_subset (s := integrableExpSet X μ) ht
  apply (integrable_tilted_iff hi _).mpr
  have hh := (integrable_nonnegative_density_iff μ H hH hH0 _).mp
    (integrable_pow_mul_exp_of_mem_interior_integrableExpSet htH n)
  simpa only [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hh

end SRWTightness
