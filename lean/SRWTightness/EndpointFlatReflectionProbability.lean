import SRWTightness.DyadicFlatPathEvent
import SRWTightness.FlatBridgeProductIntegral
import SRWTightness.GaussianReflectionMass

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The full endpoint/bridge barrier probability follows from the original reflection input. -/
theorem endpoint_flat_reflection_probability (hReflection : BridgeReflectionInput)
    (T q : ℝ) (hT : 0 < T) (hq : 0 < q) :
    ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).real
      (endpointFlatProductEvent T q) =
      (gaussianReal 0 T.toNNReal).real (Set.Icc (-q) q) := by
  let μ := gaussianReal 0 T.toNNReal
  let g : ℝ → ℝ := fun b ↦ 1 - Real.exp (-(2 * q * (q - b) / T))
  rw [product_event_real_integral _ _ _ (endpointFlatProductEvent_measurable T q)]
  have he : (fun b ↦ gaussianCoefficientLaw.real
      (Prod.mk b ⁻¹' endpointFlatProductEvent T q)) =ᵐ[μ] (Set.Iio q).indicator g := by
    letI : NullSingletonClass μ :=
      nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hT))
    have hne : ∀ᵐ b ∂μ, b ≠ q := by simp [ae_iff]
    filter_upwards [hne] with b hb
    rw [endpointFlatProductEvent_section]
    by_cases hlt : b < q
    · rw [Set.indicator_of_mem (show b ∈ Set.Iio q from hlt)]
      exact hReflection T b q hT hq hlt
    · rw [Set.indicator_of_notMem (show b ∉ Set.Iio q from hlt)]
      have hqb : q < b := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hb)
      have hempty : bridgeFlatEvent T b q = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        have hh := hω T ⟨hT.le, le_rfl⟩
        rw [endpointBrownianBridge_terminal T b hT] at hh
        exact (not_le_of_gt hqb) hh
      rw [hempty, measureReal_empty]
  rw [integral_congr_ae he, integral_indicator measurableSet_Iio]
  rw [gaussian_real_set_integral_density g (Set.Iio q) measurableSet_Iio T hT]
  exact gaussian_reflection_mass T q hT hq.le

end SRWTightness
