import SRWTightness.PositiveBridgeCrossingEvent
import SRWTightness.BesselCurvedDecay

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Transfer full-time continuous-boundary crossing probabilities through half-path domination. -/
theorem positiveBridge_crossing_comparison (hBridge : PositiveBridgeRestrictionInput)
    (hPositive : BesselThreePositiveInput) (T x y s M : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (hsT : s ≤ T / 2)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M)
    (bound : ℝ → ℝ) (hb : Continuous bound) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, positiveEndpointBridge T x y t ω < bound t} ≤
    (8 * Real.exp M) * (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, actualBesselThree T x t ω < bound t} := by
  rw [positiveBridge_crossing_real T x y s bound hb]
  have hdom := positiveBridge_path_domination hBridge hPositive T x y s M
    hT hx hy hs hsT hxy hM
  have hreal : ((positiveBridgeCoefficientLaw T x y).map
      (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y t ω)).real
        (dyadicLowerPathEvent s bound) ≤
      (ENNReal.ofReal (8 * Real.exp M) • (independentBridgeLaw (Fin 3)).map
        (fun ω (t : Set.Icc (0 : ℝ) s) ↦ actualBesselThree T x t ω)).real
          (dyadicLowerPathEvent s bound) :=
    ENNReal.toReal_mono (by
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply (actualBesselThree_path_measurable T x s)
          (dyadicLowerPathEvent_measurable s bound)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (hdom (dyadicLowerPathEvent s bound))
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (by positivity),
    map_measureReal_apply (actualBesselThree_path_measurable T x s)
      (dyadicLowerPathEvent_measurable s bound)] at hreal
  apply hreal.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨n, j, hj, hcross⟩
  exact ⟨(j : ℝ) / 2 ^ n, ⟨by positivity, hj⟩, hcross⟩

/-- The first-half curved crossing estimate for the actual positive bridge. -/
theorem positiveBridge_curved_first_half (hBridge : PositiveBridgeRestrictionInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C)
    (T x y H γ M : ℝ) (hT : 0 < T) (hH : 0 < H) (hx : Real.sqrt H ≤ x)
    (hy : 0 < y) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) (T / 2),
        positiveEndpointBridge T x y t ω < (H + t) ^ γ} ≤
      (8 * Real.exp M) *
        (((2 : ℝ) ^ γ + C * (3 : ℝ) ^ γ / (1 - (2 : ℝ) ^ (γ - 1 / 2))) *
          H ^ (γ - 1 / 2)) := by
  have hx0 : 0 < x := (Real.sqrt_pos.mpr hH).trans_le hx
  have hb : Continuous (fun t : ℝ ↦ (H + t) ^ γ) :=
    (Real.continuous_rpow_const hγ).comp (continuous_const.add continuous_id)
  have hc := positiveBridge_crossing_comparison hBridge hPositive T x y (T / 2) M
    hT hx0 hy (by positivity) le_rfl hxy hM (fun t ↦ (H + t) ^ γ) hb
  have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) (T / 2),
      actualBesselThree T x t ω < (H + t) ^ γ} ⊆ besselCurvedCrossing T x H γ 0 T := by
    rintro ω ⟨t, ht, hcross⟩
    exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, hcross⟩
  exact hc.trans (mul_le_mul_of_nonneg_left
    ((measureReal_mono hsub).trans (besselCurvedCrossing_power_decay hInitial hHit C hMoment
      T x H γ hT hH hx hγ hγhalf)) (by positivity))

end SRWTightness
