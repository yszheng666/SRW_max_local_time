import SRWTightness.KilledBrownianDoobPastProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Distance-path past events under the actual Doob law use the exact Bessel transition kernel. -/
theorem killed_brownian_doob_radial_past_probability (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrT : r < T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (killedBrownianDoobCoefficientLaw T x).real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ x - Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      x - Real.sqrt T * gaussianDyadicPath ω (T / T) ∈ B} =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ x - Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A},
      (besselDensityLaw (T - r) (x - Real.sqrt T * gaussianDyadicPath ω (r / T))).real B
        ∂killedBrownianDoobCoefficientLaw T x := by
  let H := fun p : Set.Icc (0 : ℝ) r → ℝ ↦ fun u ↦ x - p u
  have hH : Measurable H := measurable_pi_lambda _ (fun u ↦
    measurable_const.sub (measurable_pi_apply u))
  exact killed_brownian_doob_past_probability hReflection T x r hT hx hr hrT
    (H ⁻¹' A) (hA.preimage hH) B hB

end SRWTightness
