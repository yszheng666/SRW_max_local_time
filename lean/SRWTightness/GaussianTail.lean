import SRWTightness.GaussianField
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory

namespace SRWTightness

 theorem gaussianGreenLaw_subgaussian (D A : Finset Site) (hAD : A ⊆ D) (z : A) :
    HasSubgaussianMGF (fun φ : EuclideanSpace ℝ A ↦ φ z)
      (killedGreen D z z).toNNReal (gaussianGreenLaw D A) := by
  have hmap := gaussianGreenLaw_coordinate D A hAD z
  constructor
  · intro t
    exact hmap.integrable_comp_of_integrable (integrable_exp_mul_gaussianReal t)
  · intro t
    rw [mgf_gaussianReal hmap.map_eq]
    simp

 theorem gaussianGreenLaw_coordinate_tail (D A : Finset Site) (hAD : A ⊆ D)
    (z : A) (s : ℝ) (hs : 0 ≤ s) :
    (gaussianGreenLaw D A).real {φ | s ≤ φ z} ≤
      Real.exp (-s ^ 2 / (2 * killedGreen D z z)) := by
  have he := (gaussianGreenLaw_subgaussian D A hAD z).measure_ge_le hs
  simpa only [Real.coe_toNNReal _ (killedGreen_nonneg D z z)] using he

 theorem gaussianGreenLaw_max_tail (D A : Finset Site) (hAD : A ⊆ D)
    (s : ℝ) (hs : 0 ≤ s) :
    (gaussianGreenLaw D A).real {φ | ∃ z : A, s ≤ φ z} ≤
      ∑ z : A, Real.exp (-s ^ 2 / (2 * killedGreen D z z)) := by
  have he : {φ : EuclideanSpace ℝ A | ∃ z : A, s ≤ φ z} =
      ⋃ z : A, {φ : EuclideanSpace ℝ A | s ≤ φ z} := by ext φ; simp
  rw [he]
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun z _ ↦ gaussianGreenLaw_coordinate_tail D A hAD z s hs))

end SRWTightness
