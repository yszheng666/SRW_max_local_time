import SRWTightness.GaussianCoefficientSpace
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

theorem gaussianCoefficient_subgaussian (i : GaussianCoefficientIndex) :
    HasSubgaussianMGF (fun ω : GaussianCoefficientSpace ↦ ω i) 1
      gaussianCoefficientLaw := by
  apply (HasSubgaussianMGF.id_map_iff (measurable_pi_apply i).aemeasurable).mp
  rw [gaussianCoefficient_map]
  constructor
  · intro t
    exact integrable_exp_mul_gaussianReal t
  · intro t
    simp [mgf_id_gaussianReal]

theorem gaussianCoefficient_tail (i : GaussianCoefficientIndex) (r : ℝ) (hr : 0 ≤ r) :
    gaussianCoefficientLaw.real {ω | r ≤ |ω i|} ≤ 2 * Real.exp (-r ^ 2 / 2) := by
  have hp := (gaussianCoefficient_subgaussian i).measure_ge_le hr
  have hn := (gaussianCoefficient_subgaussian i).neg.measure_ge_le hr
  have he : {ω : GaussianCoefficientSpace | r ≤ |ω i|} =
      {ω | r ≤ ω i} ∪ {ω | r ≤ -ω i} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [he]
  have hu := measureReal_union_le (μ := gaussianCoefficientLaw)
    {ω | r ≤ ω i} {ω | r ≤ -ω i}
  simp only [NNReal.coe_one, mul_one, Pi.neg_apply] at hp hn
  linarith

theorem gaussianCoefficient_layer_tail (n N : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    gaussianCoefficientLaw.real {ω | ∃ k < N, r ≤ |ω (some (n, k))|} ≤
      (N : ℝ) * (2 * Real.exp (-r ^ 2 / 2)) := by
  have he : {ω : GaussianCoefficientSpace | ∃ k < N, r ≤ |ω (some (n, k))|} =
      ⋃ k ∈ Finset.range N, {ω | r ≤ |ω (some (n, k))|} := by
    ext ω
    simp
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        gaussianCoefficientLaw.real {ω | r ≤ |ω (some (n, k))|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range N, 2 * Real.exp (-r ^ 2 / 2) :=
      Finset.sum_le_sum (fun k _ ↦ gaussianCoefficient_tail _ r hr)
    _ = _ := by simp

end SRWTightness
