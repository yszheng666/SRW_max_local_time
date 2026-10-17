import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

/-- A centered Gaussian variable is sub-Gaussian with any upper bound for its variance. -/
theorem gaussian_centered_subgaussian_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : HasGaussianLaw X μ)
    (hm : (∫ ω, X ω ∂μ) = 0) (v : ℝ≥0) (hv : Var[X; μ] ≤ v) :
    HasSubgaussianMGF X v μ := by
  apply (HasSubgaussianMGF.id_map_iff hX.aemeasurable).mp
  rw [hX.map_eq_gaussianReal, hm]
  constructor
  · intro t
    exact integrable_exp_mul_gaussianReal t
  · intro t
    rw [mgf_id_gaussianReal]
    simp only [zero_mul, zero_add, Real.coe_toNNReal _ (variance_nonneg X μ)]
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv (sq_nonneg t))
      (by norm_num)

/-- A sub-Gaussian variance bound controls the closed absolute tail, including zero variance. -/
theorem subgaussian_closed_absolute_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (v : ℝ≥0)
    (hX : HasSubgaussianMGF X v μ) (u : ℝ) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * (v : ℝ))) := by
  have hp := hX.measure_ge_le hu
  have hn := hX.neg.measure_ge_le hu
  have he : {ω | u ≤ |X ω|} = {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [he]
  have hh := measureReal_union_le (μ := μ) {ω | u ≤ X ω} {ω | u ≤ -X ω}
  simp only [Pi.neg_apply] at hn
  linarith

end SRWTightness
