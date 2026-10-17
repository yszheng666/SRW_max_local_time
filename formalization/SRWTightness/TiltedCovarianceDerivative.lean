import SRWTightness.JointCenteredThirdIdentity
import SRWTightness.WeightedTiltedIntegrability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Differentiating an actual tilted covariance gives the joint third centered moment. -/
theorem hasDerivAt_tilted_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H J X : Ω → ℝ)
    (hH : Measurable H) (hJ : Measurable J)
    (hH0 : ∀ ω, 0 ≤ H ω) (hJ0 : ∀ ω, 0 ≤ J ω) (t : ℝ)
    (ht : t ∈ interior (integrableExpSet X μ))
    (htH : t ∈ interior (integrableExpSet X
      (μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω)))))
    (htJ : t ∈ interior (integrableExpSet X
      (μ.withDensity (fun ω ↦ ENNReal.ofReal (J ω)))))
    (htHJ : t ∈ interior (integrableExpSet X
      (μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω * J ω))))) :
    let ν := μ.tilted (fun ω ↦ t * X ω)
    HasDerivAt (fun s ↦ covariance H J (μ.tilted (fun ω ↦ s * X ω)))
      (∫ ω, (H ω - ∫ a, H a ∂ν) * (J ω - ∫ a, J a ∂ν) *
        (X ω - ∫ a, X a ∂ν) ∂ν) t := by
  let ν := μ.tilted (fun ω ↦ t * X ω)
  have hiExp := interior_subset (s := integrableExpSet X μ) ht
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hiExp
  have hHJ : Measurable (fun ω ↦ H ω * J ω) := hH.mul hJ
  have hHJ0 (ω : Ω) : 0 ≤ H ω * J ω := mul_nonneg (hH0 ω) (hJ0 ω)
  have hi (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
      (r : ℝ) (hr : r ∈ interior (integrableExpSet X μ))
      (hrW : r ∈ interior (integrableExpSet X
        (μ.withDensity (fun ω ↦ ENNReal.ofReal (W ω))))) :
      Integrable W (μ.tilted (fun ω ↦ r * X ω)) ∧
      Integrable (fun ω ↦ W ω * X ω) (μ.tilted (fun ω ↦ r * X ω)) := by
    constructor
    · simpa only [pow_zero, mul_one] using weighted_tilted_pow_integrable μ W X hW hW0 r hr hrW 0
    · simpa only [pow_one] using weighted_tilted_pow_integrable μ W X hW hW0 r hr hrW 1
  have hiH := hi H hH hH0 t ht htH
  have hiJ := hi J hJ hJ0 t ht htJ
  have hiHJ := hi (fun ω ↦ H ω * J ω) hHJ hHJ0 t ht htHJ
  have hiX : Integrable X ν := by
    apply (integrable_tilted_iff hiExp _).mpr
    simpa only [pow_one, smul_eq_mul, mul_comm] using
      integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 1
  have hEq : (fun s ↦ covariance H J (μ.tilted (fun ω ↦ s * X ω))) =ᶠ[𝓝 t]
      (fun s ↦ (∫ ω, H ω * J ω ∂μ.tilted (fun ω ↦ s * X ω)) -
        (∫ ω, H ω ∂μ.tilted (fun ω ↦ s * X ω)) *
          (∫ ω, J ω ∂μ.tilted (fun ω ↦ s * X ω))) := by
    filter_upwards [isOpen_interior.eventually_mem ht, isOpen_interior.eventually_mem htH,
      isOpen_interior.eventually_mem htJ, isOpen_interior.eventually_mem htHJ] with r hr hrH hrJ hrHJ
    letI : IsProbabilityMeasure (μ.tilted (fun ω ↦ r * X ω)) :=
      isProbabilityMeasure_tilted (interior_subset (s := integrableExpSet X μ) hr)
    exact covariance_eq_sub_of_integrable _ H J
      (hi H hH hH0 r hr hrH).1 (hi J hJ hJ0 r hr hrJ).1
      (hi (fun ω ↦ H ω * J ω) hHJ hHJ0 r hr hrHJ).1
  have hder := (hasDerivAt_tilted_mean μ (fun ω ↦ H ω * J ω) X hHJ hHJ0 t ht htHJ).sub
    ((hasDerivAt_tilted_mean μ H X hH hH0 t ht htH).mul
      (hasDerivAt_tilted_mean μ J X hJ hJ0 t ht htJ))
  have hval : covariance (fun ω ↦ H ω * J ω) X ν -
      (covariance H X ν * (∫ ω, J ω ∂ν) + (∫ ω, H ω ∂ν) * covariance J X ν) =
        ∫ ω, (H ω - ∫ a, H a ∂ν) * (J ω - ∫ a, J a ∂ν) * (X ω - ∫ a, X a ∂ν) ∂ν := by
    rw [joint_centered_third_covariance_identity ν H J X hiH.1 hiJ.1 hiX hiHJ.1 hiH.2 hiJ.2 hiHJ.2]
    ring
  rw [hval] at hder
  exact hEq.hasDerivAt_iff.mpr hder

end SRWTightness
