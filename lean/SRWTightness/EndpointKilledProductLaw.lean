import SRWTightness.KilledBrownianDensityLaw
import SRWTightness.BridgeFlatEndpointReflection

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The endpoint law under the full flat bridge event has the literal killed Brownian density. -/
theorem endpoint_killed_product_law (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) (A : Set ℝ) (hA : MeasurableSet A) :
    ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).real
      {p | x - p.1 ∈ A ∧ p ∈ endpointFlatProductEvent T x} =
      (killedBrownianDensityLaw T x).real A := by
  let μ := gaussianReal 0 T.toNNReal
  let E : Set (ℝ × GaussianCoefficientSpace) :=
    {p | x - p.1 ∈ A ∧ p ∈ endpointFlatProductEvent T x}
  let g : ℝ → ℝ := fun b ↦ 1 - Real.exp (-(2 * x * (x - b) / T))
  have hE : MeasurableSet E :=
    (hA.preimage (measurable_const.sub measurable_fst)).inter
      (endpointFlatProductEvent_measurable T x)
  have hsection (b : ℝ) : gaussianCoefficientLaw.real (Prod.mk b ⁻¹' E) =
      gaussianCoefficientLaw.real (bridgeFlatEvent T b x) * A.indicator (fun _ ↦ 1) (x - b) := by
    by_cases hb : x - b ∈ A
    · have he : Prod.mk b ⁻¹' E = Prod.mk b ⁻¹' endpointFlatProductEvent T x := by
        ext ω
        simp only [E, Set.mem_preimage, Set.mem_setOf_eq, hb, true_and]
      rw [he, endpointFlatProductEvent_section, Set.indicator_of_mem hb, mul_one]
    · have he : Prod.mk b ⁻¹' E = ∅ := by
        ext ω
        simp only [E, Set.mem_preimage, Set.mem_setOf_eq, hb, false_and, Set.mem_empty_iff_false]
      rw [he, measureReal_empty, Set.indicator_of_notMem hb, mul_zero]
  rw [product_event_real_integral _ _ E hE]
  simp_rw [hsection]
  have he : (fun b ↦ gaussianCoefficientLaw.real (bridgeFlatEvent T b x) *
      A.indicator (fun _ ↦ 1) (x - b)) =ᵐ[μ]
      (Set.Iio x).indicator (fun b ↦ g b * A.indicator (fun _ ↦ 1) (x - b)) := by
    filter_upwards [bridge_flat_endpoint_reflection hReflection T x hT hx] with b hb
    rw [hb]
    by_cases hbx : b ∈ Set.Iio x
    · simp only [Set.indicator_of_mem hbx]
      rfl
    · simp only [Set.indicator_of_notMem hbx, zero_mul]
  rw [integral_congr_ae he, integral_indicator measurableSet_Iio,
    gaussian_real_set_integral_density _ (Set.Iio x) measurableSet_Iio T hT]
  calc
    _ = ∫ y in Set.Ioi (0 : ℝ), killedBrownianDensity T x y *
        A.indicator (fun _ ↦ 1) y := by
      simpa only [g, mul_assoc] using
        killed_gaussian_reflection_integral T x hT (A.indicator (fun _ ↦ 1))
    _ = ∫ y, A.indicator (fun _ ↦ 1) y ∂killedBrownianDensityLaw T x :=
      (killed_brownian_density_law_integral T x hT hx _).symm
    _ = _ := integral_indicator_one hA

end SRWTightness
