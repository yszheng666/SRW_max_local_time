import SRWTightness.SquaredGaussianLaws
import SRWTightness.LaplaceUniqueness
import SRWTightness.ProjectedOccupation

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

/-- The occupation/Gaussian isomorphism for the actual killed SRW occupation law. -/
theorem occupation_gaussian_isomorphism (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (r : ℝ≥0) :
    occupationPlusGaussianSquareLaw D A α r =
      shiftedGaussianSquareLaw D A ((r : ℝ) * α) := by
  letI := occupationPlusGaussianSquareLaw_isProbabilityMeasure D A α hα hcap r
  apply measure_eq_of_laplace_eq_nonneg _ _
    (occupationPlusGaussianSquareLaw_nonneg D A α r)
    (shiftedGaussianSquareLaw_nonneg D A ((r : ℝ) * α))
  intro f hf
  rw [occupationPlusGaussianSquareLaw_laplace D A α hα hcap,
    shiftedGaussianSquareLaw_laplace,
    gaussianGreenSquaredLaplace_constant_shift D A hAD f hf _ (mul_nonneg r.coe_nonneg hα),
    continuousOccupation_laplace D A hAD α hα hcap r f hf]
  rw [neg_mul, mul_comm]

/-- Manuscript (3.7), for observation inside an arbitrary larger reference set. -/
theorem projected_occupation_gaussian_isomorphism (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (r : ℝ≥0) :
    ((projectedOccupationLaw D A K hAK α r).prod (gaussianGreenLaw D A)).map
      (fun p z ↦ p.1 z + (p.2 z) ^ 2 / 2) =
        shiftedGaussianSquareLaw D A ((r : ℝ) * α) := by
  rw [projectedOccupationLaw_eq D A K hAK hKD α hα hcap r]
  exact occupation_gaussian_isomorphism D A (hAK.trans hKD) α hα
    ((mul_le_mul_of_nonneg_left (capacity_mono_set D A K hAK hKD) hα).trans hcap) r

end SRWTightness
