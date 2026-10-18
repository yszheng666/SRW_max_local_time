import SRWTightness.GaussianField

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

theorem symmetric_probability_nonnegative (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun x ↦ -x) = μ) : (1 / 2 : ℝ) ≤ μ.real (Set.Ici 0) := by
  have he : μ.real (Set.Ici 0) = μ.real (Set.Iic 0) := by
    conv_lhs => rw [← hμ]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Ici]
    congr 1
    ext x
    simp
  have hu := measureReal_union_le (μ := μ) (Set.Iic (0 : ℝ)) (Set.Ici 0)
  rw [Set.Iic_union_Ici, probReal_univ, ← he] at hu
  linarith

theorem gaussianReal_zero_nonnegative (v : ℝ≥0) :
    (1 / 2 : ℝ) ≤ (gaussianReal 0 v).real (Set.Ici 0) := by
  apply symmetric_probability_nonnegative
  simpa using (gaussianReal_map_neg (μ := 0) (v := v))

theorem multivariateGaussian_zero_coordinate_nonnegative {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (z : ι) :
    (1 / 2 : ℝ) ≤ (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
      {φ | 0 ≤ φ z} := by
  have hp := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ ι)) hS (i := z)).map_eq
  simp only [WithLp.ofLp_zero, Pi.zero_apply] at hp
  have he := gaussianReal_zero_nonnegative (S z z).toNNReal
  rw [← hp, map_measureReal_apply (by fun_prop) measurableSet_Ici] at he
  exact he

end SRWTightness
