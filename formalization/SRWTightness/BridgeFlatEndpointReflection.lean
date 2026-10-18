import SRWTightness.EndpointFlatReflectionProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Under the endpoint Gaussian law, the bridge survival probability is the reflected factor. -/
theorem bridge_flat_endpoint_reflection (hReflection : BridgeReflectionInput)
    (T q : ℝ) (hT : 0 < T) (hq : 0 < q) :
    (fun b ↦ gaussianCoefficientLaw.real (bridgeFlatEvent T b q)) =ᵐ[gaussianReal 0 T.toNNReal]
      (Set.Iio q).indicator (fun b ↦ 1 - Real.exp (-(2 * q * (q - b) / T))) := by
  letI : NullSingletonClass (gaussianReal 0 T.toNNReal) :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hT))
  have hne : ∀ᵐ b ∂gaussianReal 0 T.toNNReal, b ≠ q := by simp [ae_iff]
  filter_upwards [hne] with b hb
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

end SRWTightness
