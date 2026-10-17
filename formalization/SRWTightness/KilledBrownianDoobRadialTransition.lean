import SRWTightness.KilledBrownianDoobRadialPastProbability
import SRWTightness.KilledBrownianDoobRadialPrefixLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Every later time of the actual Doob path has the Bessel kernel
conditional on its radial past. -/
theorem killed_brownian_doob_radial_transition (hReflection : BridgeReflectionInput)
    (T x r t : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrt : r < t) (htT : t ≤ T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (killedBrownianDoobCoefficientLaw T x).real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ x - Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A ∧
      x - Real.sqrt T * gaussianDyadicPath ω (t / T) ∈ B} =
    ∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ x - Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ A},
      (besselDensityLaw (t - r) (x - Real.sqrt T * gaussianDyadicPath ω (r / T))).real B
        ∂killedBrownianDoobCoefficientLaw T x := by
  have ht : 0 < t := hr.trans hrt
  let P := fun S ω (u : Set.Icc (0 : ℝ) t) ↦
    x - Real.sqrt S * gaussianDyadicPath ω (u / S)
  let H := fun p : Set.Icc (0 : ℝ) t → ℝ ↦
    fun u : Set.Icc (0 : ℝ) r ↦ p ⟨u, u.property.1, u.property.2.trans hrt.le⟩
  let e : Set.Icc (0 : ℝ) t := ⟨t, ht.le, le_rfl⟩
  let d : Set.Icc (0 : ℝ) t := ⟨r, hr.le, hrt.le⟩
  let C : Set (Set.Icc (0 : ℝ) t → ℝ) := {p | H p ∈ A ∧ p e ∈ B}
  let k := fun p : Set.Icc (0 : ℝ) t → ℝ ↦ (besselDensityLaw (t - r) (p d)).real B
  have hP (S : ℝ) : Measurable (P S) := measurable_pi_lambda _ (fun _ ↦
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _)))
  have hH : Measurable H := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  have hC : MeasurableSet C := (hA.preimage hH).inter
    (hB.preimage (measurable_pi_apply e))
  have hk : Measurable k := (bessel_kernel_measurable (t - r) B hB).comp
    (measurable_pi_apply d)
  have he : (killedBrownianDoobCoefficientLaw T x).map (P T) =
      (killedBrownianDoobCoefficientLaw t x).map (P t) :=
    killed_brownian_doob_radial_prefix_law hReflection T x t hT hx ht htT
  have hprob : (killedBrownianDoobCoefficientLaw T x).real (P T ⁻¹' C) =
      (killedBrownianDoobCoefficientLaw t x).real (P t ⁻¹' C) := by
    rw [← map_measureReal_apply (hP T) hC, ← map_measureReal_apply (hP t) hC, he]
  have hint : (∫ ω in P T ⁻¹' (H ⁻¹' A), k (P T ω)
      ∂killedBrownianDoobCoefficientLaw T x) =
      ∫ ω in P t ⁻¹' (H ⁻¹' A), k (P t ω)
        ∂killedBrownianDoobCoefficientLaw t x := by
    rw [← setIntegral_map (hA.preimage hH) hk.aestronglyMeasurable (hP T).aemeasurable,
      ← setIntegral_map (hA.preimage hH) hk.aestronglyMeasurable (hP t).aemeasurable, he]
  change (killedBrownianDoobCoefficientLaw T x).real (P T ⁻¹' C) =
    ∫ ω in P T ⁻¹' (H ⁻¹' A), k (P T ω) ∂killedBrownianDoobCoefficientLaw T x
  rw [hprob, hint]
  exact killed_brownian_doob_radial_past_probability hReflection t x r ht hx hr hrt A hA B hB

end SRWTightness
