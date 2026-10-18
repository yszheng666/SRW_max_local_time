import SRWTightness.KilledBrownianDoobRadialPastProbability
import SRWTightness.KilledBrownianDoobMarginal
import SRWTightness.BesselRadialPastProbability
import SRWTightness.JointLawFromPastKernel

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Doob and Bessel processes have the same joint law
at an earlier time and the horizon. -/
theorem killed_brownian_doob_bessel_pair_law (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrT : r < T) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω ↦ (x - Real.sqrt T * gaussianDyadicPath ω (r / T),
        x - Real.sqrt T * gaussianDyadicPath ω (T / T))) =
    (independentBridgeLaw (Fin 3)).map
      (fun ω ↦ (actualBesselThree T x r ω, actualBesselThree T x T ω)) := by
  letI := killed_brownian_doob_probability hReflection T x hT hx
  let D := fun t ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (t / T)
  have hD (t : ℝ) : Measurable (D t) :=
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _))
  let e : Set.Icc (0 : ℝ) r := ⟨r, hr.le, le_rfl⟩
  apply joint_law_from_past_kernel (killedBrownianDoobCoefficientLaw T x)
    (independentBridgeLaw (Fin 3)) (D r) (actualBesselThree T x r)
    (D T) (actualBesselThree T x T) (hD r) (actualBesselThree_measurable T x r)
    (hD T) (actualBesselThree_measurable T x T)
    (fun B z ↦ (besselDensityLaw (T - r) z).real B)
    (fun B hB ↦ bessel_kernel_measurable (T - r) B hB)
    (killed_brownian_doob_bessel_marginal hReflection T x r hT hx hr hrT.le)
  · intro A B hA hB
    exact killed_brownian_doob_radial_past_probability hReflection T x r hT hx hr hrT
      ((fun p : Set.Icc (0 : ℝ) r → ℝ ↦ p e) ⁻¹' A)
      (hA.preimage (measurable_pi_apply e)) B hB
  · intro A B hA hB
    exact bessel_radial_past_probability T x r T hT hx hr hrT le_rfl
      ((fun p : Set.Icc (0 : ℝ) r → ℝ ↦ p e) ⁻¹' A)
      (hA.preimage (measurable_pi_apply e)) B hB

end SRWTightness
