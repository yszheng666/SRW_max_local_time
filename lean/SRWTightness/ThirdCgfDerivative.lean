import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- The third cgf derivative expressed through the actual exponentially weighted moments. -/
theorem iteratedDeriv_three_cgf_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (t : ℝ)
    (ht : t ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 3 (cgf X μ) t =
      (∫ ω, X ω ^ 3 * Real.exp (t * X ω) ∂μ) / mgf X μ t -
      3 * (∫ ω, X ω ^ 2 * Real.exp (t * X ω) ∂μ) *
        (∫ ω, X ω * Real.exp (t * X ω) ∂μ) / mgf X μ t ^ 2 +
      2 * (∫ ω, X ω * Real.exp (t * X ω) ∂μ) ^ 3 / mgf X μ t ^ 3 := by
  let N := fun (n : ℕ) (v : ℝ) ↦ ∫ ω, X ω ^ n * Real.exp (v * X ω) ∂μ
  have h0 : HasDerivAt (mgf X μ) (N 1 t) t := by simpa [N] using hasDerivAt_mgf ht
  have h1 : HasDerivAt (N 1) (N 2 t) t := hasDerivAt_integral_pow_mul_exp_real ht 1
  have h2 : HasDerivAt (N 2) (N 3 t) t := hasDerivAt_integral_pow_mul_exp_real ht 2
  have hz : mgf X μ t ≠ 0 := (mgf_pos (interior_subset (s := integrableExpSet X μ) ht)).ne'
  have hEq : iteratedDeriv 2 (cgf X μ) =ᶠ[𝓝 t]
      (fun v ↦ N 2 v / mgf X μ v - (N 1 v / mgf X μ v) ^ 2) := by
    filter_upwards [isOpen_interior.eventually_mem ht] with v hv
    rw [iteratedDeriv_two_cgf hv, deriv_cgf hv]
    simp only [N, pow_one]
  have hder := (h2.div h0 hz).sub ((h1.div h0 hz).pow 2)
  rw [iteratedDeriv_succ, hEq.deriv_eq]
  change deriv (N 2 / mgf X μ - (N 1 / mgf X μ) ^ 2) t = _
  rw [hder.deriv]
  dsimp [N]
  simp only [pow_one]
  field_simp [hz]
  ring_nf
  simp only [mul_comm]

end SRWTightness
