import SRWTightness.ScaledGaussianKilledProbability
import SRWTightness.ScaledGaussianBarrierBoundary

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Under strict positive survival, the actual Brownian endpoint has the killed density. -/
theorem scaled_gaussian_killed_strict_probability (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) (A : Set ℝ) (hA : MeasurableSet A) :
    gaussianCoefficientLaw.real {ω |
      x - Real.sqrt T * gaussianDyadicPath ω (T / T) ∈ A ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < x - Real.sqrt T * gaussianDyadicPath ω (t / T)} =
      (killedBrownianDensityLaw T x).real A := by
  rw [← scaled_gaussian_killed_probability hReflection T x hT hx A hA]
  apply measureReal_congr
  filter_upwards [scaled_gaussian_barrier_boundary hReflection T x hT hx] with ω hω
  apply propext
  simp only [Set.mem_setOf_eq, sub_pos]
  exact and_congr_right (fun _ ↦ hω)

end SRWTightness
