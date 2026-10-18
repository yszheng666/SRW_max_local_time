import SRWTightness.PositiveBridgeSecondHalfIncrement

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- All bridge intervals have a linear second-moment bound, including intervals across the midpoint. -/
theorem positiveBridge_full_increment (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hIncrement : BesselThreeIncrementInput) (T x y M r s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hy : 0 < y)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ T)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    Integrable (fun ω ↦
      (positiveEndpointBridge T x y s ω - positiveEndpointBridge T x y r ω) ^ 2)
      (positiveBridgeCoefficientLaw T x y) ∧
    (∫ ω, (positiveEndpointBridge T x y s ω - positiveEndpointBridge T x y r ω) ^ 2
      ∂positiveBridgeCoefficientLaw T x y) ≤ 48 * Real.exp M * (s - r) := by
  by_cases hleft : s ≤ T / 2
  · have h := positiveBridge_first_half_increment hBridge hPositive hIncrement
      T x y M r s hT hx hy hr hrs hleft hxy hM
    refine ⟨h.1, h.2.trans ?_⟩
    nlinarith [Real.exp_pos M, mul_nonneg (Real.exp_pos M).le (sub_nonneg.mpr hrs)]
  by_cases hright : T / 2 ≤ r
  · have h := positiveBridge_second_half_increment hBridge hReverse hPositive hIncrement
      T x y M r s hT hx hy hright hrs hs hxy hM
    refine ⟨h.1, h.2.trans ?_⟩
    nlinarith [Real.exp_pos M, mul_nonneg (Real.exp_pos M).le (sub_nonneg.mpr hrs)]
  have hL := positiveBridge_first_half_increment hBridge hPositive hIncrement
    T x y M r (T / 2) hT hx hy hr (le_of_not_ge hright) le_rfl hxy hM
  have hR := positiveBridge_second_half_increment hBridge hReverse hPositive hIncrement
    T x y M (T / 2) s hT hx hy le_rfl (le_of_not_ge hleft) hs hxy hM
  let f := fun ω ↦ (positiveEndpointBridge T x y s ω - positiveEndpointBridge T x y r ω) ^ 2
  let g := fun ω ↦
    2 * (positiveEndpointBridge T x y (T / 2) ω - positiveEndpointBridge T x y r ω) ^ 2 +
    2 * (positiveEndpointBridge T x y s ω - positiveEndpointBridge T x y (T / 2) ω) ^ 2
  have hg : Integrable g (positiveBridgeCoefficientLaw T x y) :=
    (hL.1.const_mul 2).add (hR.1.const_mul 2)
  have hfg : ∀ ω, f ω ≤ g ω := by
    intro ω
    dsimp [f, g]
    nlinarith [sq_nonneg (positiveEndpointBridge T x y s ω +
      positiveEndpointBridge T x y r ω - 2 * positiveEndpointBridge T x y (T / 2) ω)]
  have hf : Integrable f (positiveBridgeCoefficientLaw T x y) :=
    hg.mono_nonneg
      (((positiveEndpointBridge_measurable T x y s).sub
        (positiveEndpointBridge_measurable T x y r)).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω ↦ sq_nonneg _))
      (Filter.Eventually.of_forall hfg)
  refine ⟨hf, ?_⟩
  have hle := integral_mono_ae hf hg (Filter.Eventually.of_forall hfg)
  change (∫ ω, f ω ∂positiveBridgeCoefficientLaw T x y) ≤ _
  apply hle.trans
  dsimp [g]
  rw [integral_add (hL.1.const_mul 2) (hR.1.const_mul 2),
    integral_const_mul, integral_const_mul]
  nlinarith [hL.2, hR.2]

end SRWTightness
