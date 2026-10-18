import SRWTightness.KilledBrownianDoobPastEndpoint
import SRWTightness.KilledBrownianDoobPrefixIntegral
import SRWTightness.BesselKernelMeasurable

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Doob law has the Bessel transition kernel on every positive-time past event. -/
theorem killed_brownian_doob_past_probability (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrT : r < T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (killedBrownianDoobCoefficientLaw T x).real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      x - Real.sqrt T * gaussianDyadicPath ω (T / T) ∈ B} =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A},
      (besselDensityLaw (T - r) (x - Real.sqrt T * gaussianDyadicPath ω (r / T))).real B
        ∂killedBrownianDoobCoefficientLaw T x := by
  classical
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let e : Set.Icc (0 : ℝ) r := ⟨r, hr.le, le_rfl⟩
  let k := fun p : Set.Icc (0 : ℝ) r → ℝ ↦ (besselDensityLaw (T - r) (x - p e)).real B
  let D : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | p ∈ dyadicFlatPathEvent r x ∧ p e < x}
  let w := fun p : Set.Icc (0 : ℝ) r → ℝ ↦ (x - p e) / x
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hk : Measurable k := (bessel_kernel_measurable (T - r) B hB).comp
    (measurable_const.sub (measurable_pi_apply e))
  have hval (ω) : A.indicator k (P ω) = (P ⁻¹' A).indicator (fun ω ↦ k (P ω)) ω := by
    by_cases h : P ω ∈ A <;> simp [h]
  have hwval (ω) : w (P ω) * A.indicator k (P ω) =
      (P ⁻¹' A).indicator (fun ω ↦ w (P ω) * k (P ω)) ω := by
    by_cases h : P ω ∈ A <;> simp [h]
  have he := killed_brownian_doob_prefix_integral hReflection T x r hT hx hr hrT
    (A.indicator k) (hk.indicator hA)
  have he' : (∫ ω in P ⁻¹' A, k (P ω) ∂killedBrownianDoobCoefficientLaw T x) =
      ∫ ω in (P ⁻¹' A) ∩ (P ⁻¹' D), w (P ω) * k (P ω) ∂gaussianCoefficientLaw := by
    change (∫ ω, A.indicator k (P ω) ∂killedBrownianDoobCoefficientLaw T x) =
      (∫ ω in P ⁻¹' D, w (P ω) * A.indicator k (P ω) ∂gaussianCoefficientLaw) at he
    simp_rw [hwval] at he
    simp_rw [hval] at he
    simpa only [integral_indicator (hA.preimage hP),
      setIntegral_indicator (hA.preimage hP),
      Measure.restrict_restrict (hA.preimage hP)] using he
  rw [killed_brownian_doob_past_endpoint hReflection T x r hT hx hr.le hrT A hA B hB]
  exact he'.symm

end SRWTightness
