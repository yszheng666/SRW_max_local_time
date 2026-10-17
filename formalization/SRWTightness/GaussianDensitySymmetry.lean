import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.Ring

open ProbabilityTheory
namespace SRWTightness

/-- Reflecting the argument of a Gaussian density reflects its mean. -/
theorem gaussian_density_reflect_mean (x z : ℝ) (v : NNReal) :
    gaussianPDFReal x v (-z) = gaussianPDFReal (-x) v z := by
  simp only [gaussianPDFReal_def]
  congr 2
  congr 1
  ring

/-- A Gaussian transition density is symmetric in its two spatial arguments. -/
theorem gaussian_density_spatial_symmetry (x z : ℝ) (v : NNReal) :
    gaussianPDFReal x v z = gaussianPDFReal z v x := by
  simp only [gaussianPDFReal_def]
  congr 2
  congr 1
  ring

end SRWTightness
