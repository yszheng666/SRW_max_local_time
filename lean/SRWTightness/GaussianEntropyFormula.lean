import SRWTightness.GaussianDensityEntropy
import SRWTightness.GaussianQuadraticMean

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Exact relative entropy of the actual centered Gaussian law S with respect to K. -/
theorem gaussian_density_entropy_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) :
    (∫ x, gaussianDensityWeight K S x * Real.log (gaussianDensityWeight K S x)
      ∂gaussianCoordinateLaw K) =
      (Real.log K.det - Real.log S.det - Fintype.card ι + Matrix.trace (K⁻¹ * S)) / 2 := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure S
  have he := integral_nonnegative_density (gaussianCoordinateLaw K) (gaussianDensityWeight K S)
    (gaussianDensityWeight_measurable K S) (gaussianDensityWeight_nonneg K S)
    (fun x ↦ Real.log (gaussianDensityWeight K S x))
  rw [← gaussianCoordinateLaw_changeDensity K S hK hS] at he
  rw [← he]
  simp_rw [gaussianDensityWeight_log K S hK hS]
  have hQ : Integrable (gaussianInverseCorrection K S) (gaussianCoordinateLaw S) :=
    gaussian_quadratic_integrable S (S⁻¹ - K⁻¹)
  rw [integral_sub (integrable_const _) (hQ.div_const 2), integral_const, probReal_univ,
    one_smul, integral_div, gaussianInverseCorrection_mean K S hS,
    Real.log_div (Real.sqrt_pos.mpr hK.det_pos).ne' (Real.sqrt_pos.mpr hS.det_pos).ne',
    Real.log_sqrt hK.det_pos.le, Real.log_sqrt hS.det_pos.le]
  ring

/-- The explicit matrix entropy bounds every event for two actual centered Gaussian laws. -/
theorem gaussian_trace_entropy_event_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    |(gaussianCoordinateLaw S).real s - (gaussianCoordinateLaw K).real s| ≤
      2 * Real.sqrt ((Real.log K.det - Real.log S.det - Fintype.card ι +
        Matrix.trace (K⁻¹ * S)) / 2) := by
  have hh := gaussian_entropy_event_bound K S hK hS s hs
  rwa [gaussian_density_entropy_formula K S hK hS] at hh

/-- The explicit centered Gaussian entropy bound survives independent auxiliary random variables. -/
theorem gaussian_trace_entropy_event_bound_aux {ι Ξ : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (s : Set ((ι → ℝ) × Ξ)) (hs : MeasurableSet s) :
    |((gaussianCoordinateLaw S).prod ν).real s - ((gaussianCoordinateLaw K).prod ν).real s| ≤
      2 * Real.sqrt ((Real.log K.det - Real.log S.det - Fintype.card ι +
        Matrix.trace (K⁻¹ * S)) / 2) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hd := gaussianDensityWeight_entropy_data K S hK hS
  have hh := density_entropy_event_bound_aux (gaussianCoordinateLaw K) ν (gaussianDensityWeight K S)
    (gaussianDensityWeight_measurable K S) hd.1 (gaussianDensityWeight_nonneg K S)
    hd.2.1 hd.2.2 s hs
  rw [← gaussianCoordinateLaw_changeDensity K S hK hS,
    gaussian_density_entropy_formula K S hK hS] at hh
  exact hh

end SRWTightness
