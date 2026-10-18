import SRWTightness.GaussianRadialTransitionDensity
import SRWTightness.GaussianRadialShiftBound

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Adding centered Gaussian noise to a nonzero vector gives the literal radial transition law. -/
theorem gaussian_shifted_radial_density (m : Fin 3 → ℝ) (s : ℝ) (hs : 0 < s)
    (hm : 0 < ∑ i, (m i) ^ 2) :
    HasLaw (fun z : Fin 3 → ℝ ↦ Real.sqrt (∑ i, (m i + z i) ^ 2))
      (besselDensityLaw s (Real.sqrt (∑ i, (m i) ^ 2)))
      (Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 s.toNNReal)) := by
  exact (gaussian_radial_transition_density m s _ hs (Real.sqrt_pos.mpr hm)
    (Real.sq_sqrt hm.le).symm).comp (gaussian_vector_translation_law m s.toNNReal)

end SRWTightness
