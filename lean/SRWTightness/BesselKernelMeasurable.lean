import SRWTightness.BesselDensityLaw
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
namespace SRWTightness

/-- Bessel transition probabilities are measurable in the initial radial position. -/
theorem bessel_kernel_measurable (s : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    Measurable (fun x ↦ (besselDensityLaw s x).real A) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (besselThreeDensity s p.1 p.2)) := by
    unfold besselThreeDensity killedBrownianDensity
    fun_prop
  have hi := hm.lintegral_prod_right' (ν := (volume.restrict (Set.Ioi (0 : ℝ))).restrict A)
  have he (x : ℝ) : (besselDensityLaw s x).real A =
      (∫⁻ y in A, ENNReal.ofReal (besselThreeDensity s x y)
        ∂volume.restrict (Set.Ioi (0 : ℝ))).toReal := by
    rw [Measure.real, besselDensityLaw, withDensity_apply _ hA]
  simp_rw [he]
  exact hi.ennreal_toReal

end SRWTightness
