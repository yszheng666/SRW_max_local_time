import SRWTightness.WeightedMgfDerivative

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Covariance expansion requires integrability of the factors and their product. -/
theorem covariance_eq_sub_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H X : Ω → ℝ)
    (hH : Integrable H μ) (hX : Integrable X μ)
    (hHX : Integrable (fun ω ↦ H ω * X ω) μ) :
    covariance H X μ = (∫ ω, H ω * X ω ∂μ) - (∫ ω, H ω ∂μ) * ∫ ω, X ω ∂μ := by
  simp_rw [covariance, sub_mul, mul_sub]
  repeat rw [integral_sub]
  · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ, one_smul]
    ring
  · exact hX.const_mul _
  · exact integrable_const _
  · exact hHX
  · exact hH.mul_const _
  · exact hHX.sub (hH.mul_const _)
  · exact (hX.const_mul _).sub (integrable_const _)

/-- Every tilted expectation is a ratio of exponentially weighted integrals. -/
theorem integral_tilted_observation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H X : Ω → ℝ) (s : ℝ) :
    (∫ ω, H ω ∂μ.tilted (fun ω ↦ s * X ω)) =
      (∫ ω, H ω * Real.exp (s * X ω) ∂μ) / mgf X μ s := by
  rw [integral_tilted_mul_eq_mgf, ← integral_div]
  congr 1
  funext ω
  simp only [smul_eq_mul]
  ring

/-- Linear response: differentiating a tilted mean gives its covariance with the tilt direction. -/
theorem hasDerivAt_tilted_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H X : Ω → ℝ)
    (hH : Measurable H) (hH0 : ∀ ω, 0 ≤ H ω) (t : ℝ)
    (ht : t ∈ interior (integrableExpSet X μ))
    (htH : t ∈ interior (integrableExpSet X
      (μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω))))) :
    HasDerivAt (fun s ↦ ∫ ω, H ω ∂μ.tilted (fun ω ↦ s * X ω))
      (covariance H X (μ.tilted (fun ω ↦ t * X ω))) t := by
  let ν := μ.tilted (fun ω ↦ t * X ω)
  have hi := interior_subset (s := integrableExpSet X μ) ht
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hi
  have hiH : Integrable H ν := by
    apply (integrable_tilted_iff hi _).mpr
    have hh := (integrable_nonnegative_density_iff μ H hH hH0 _).mp
      (interior_subset (s := integrableExpSet X
        (μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω)))) htH)
    simpa only [smul_eq_mul, mul_comm] using hh
  have hiX : Integrable X ν := by
    apply (integrable_tilted_iff hi _).mpr
    simpa only [pow_one, smul_eq_mul, mul_comm] using
      integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 1
  have hiHX : Integrable (fun ω ↦ H ω * X ω) ν := by
    apply (integrable_tilted_iff hi _).mpr
    have hh := (integrable_nonnegative_density_iff μ H hH hH0 _).mp
      (integrable_pow_mul_exp_of_mem_interior_integrableExpSet htH 1)
    simpa only [pow_one, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hh
  have hz : mgf X μ t ≠ 0 := (mgf_pos hi).ne'
  have hfun : (fun s ↦ ∫ ω, H ω ∂μ.tilted (fun ω ↦ s * X ω)) =
      (fun s ↦ (∫ ω, H ω * Real.exp (s * X ω) ∂μ) / mgf X μ s) := by
    funext s
    exact integral_tilted_observation μ H X s
  rw [hfun]
  have hd : HasDerivAt
      (fun s ↦ (∫ ω, H ω * Real.exp (s * X ω) ∂μ) / mgf X μ s)
      (((∫ ω, H ω * (X ω * Real.exp (t * X ω)) ∂μ) * mgf X μ t -
        (∫ ω, H ω * Real.exp (t * X ω) ∂μ) *
          (∫ ω, X ω * Real.exp (t * X ω) ∂μ)) / (mgf X μ t) ^ 2) t :=
    (hasDerivAt_weighted_mgf μ H X hH hH0 t htH).div (hasDerivAt_mgf ht) hz
  have he : ((∫ ω, H ω * (X ω * Real.exp (t * X ω)) ∂μ) * mgf X μ t -
      (∫ ω, H ω * Real.exp (t * X ω) ∂μ) *
        (∫ ω, X ω * Real.exp (t * X ω) ∂μ)) / (mgf X μ t) ^ 2 = covariance H X ν := by
    rw [covariance_eq_sub_of_integrable ν H X hiH hiX hiHX]
    dsimp only [ν]
    rw [integral_tilted_observation, integral_tilted_observation, integral_tilted_observation]
    simp only [mul_assoc]
    field_simp [hz]
    ring_nf
    simp only [mul_comm]
  rw [he] at hd
  exact hd

end SRWTightness
