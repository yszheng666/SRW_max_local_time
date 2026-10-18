import SRWTightness.KilledBrownianDensityLaw
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
namespace SRWTightness

/-- The killed endpoint probability is measurable in its initial location. -/
theorem killed_brownian_kernel_measurable (s : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    Measurable (fun x ↦ (killedBrownianDensityLaw s x).real A) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (killedBrownianDensity s p.1 p.2)) := by
    unfold killedBrownianDensity
    fun_prop
  have hi := hm.lintegral_prod_right' (ν := (volume.restrict (Set.Ioi (0 : ℝ))).restrict A)
  have he (x : ℝ) : (killedBrownianDensityLaw s x).real A =
      (∫⁻ y in A, ENNReal.ofReal (killedBrownianDensity s x y)
        ∂volume.restrict (Set.Ioi (0 : ℝ))).toReal := by
    rw [Measure.real, killedBrownianDensityLaw, withDensity_apply _ hA]
  simp_rw [he]
  exact hi.ennreal_toReal

end SRWTightness
