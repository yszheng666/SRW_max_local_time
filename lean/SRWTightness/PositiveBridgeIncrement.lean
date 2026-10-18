import SRWTightness.PositiveBridgeSurvival

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Half-bridge increments inherit the standard radial second-moment bound by path domination. -/
theorem positiveBridge_first_half_increment (hBridge : PositiveBridgeRestrictionInput)
    (hPositive : BesselThreePositiveInput) (hIncrement : BesselThreeIncrementInput)
    (T x y M r s : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ T / 2)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    Integrable (fun ω ↦
      (positiveEndpointBridge T x y s ω - positiveEndpointBridge T x y r ω) ^ 2)
      (positiveBridgeCoefficientLaw T x y) ∧
    (∫ ω, (positiveEndpointBridge T x y s ω - positiveEndpointBridge T x y r ω) ^ 2
      ∂positiveBridgeCoefficientLaw T x y) ≤ 24 * Real.exp M * (s - r) := by
  let pb := fun ω (t : Set.Icc (0 : ℝ) (T / 2)) ↦ positiveEndpointBridge T x y t ω
  let rb := fun ω (t : Set.Icc (0 : ℝ) (T / 2)) ↦ actualBesselThree T x t ω
  let F : (Set.Icc (0 : ℝ) (T / 2) → ℝ) → ℝ := fun f ↦
    (f ⟨s, hr.trans hrs, hs⟩ - f ⟨r, hr, hrs.trans hs⟩) ^ 2
  have hF : Measurable F :=
    ((measurable_pi_apply (⟨s, hr.trans hrs, hs⟩ : Set.Icc (0 : ℝ) (T / 2))).sub
      (measurable_pi_apply (⟨r, hr, hrs.trans hs⟩ : Set.Icc (0 : ℝ) (T / 2)))).pow_const 2
  have hp := positiveEndpointBridge_path_measurable T x y (T / 2)
  have hb := actualBesselThree_path_measurable T x (T / 2)
  have hI := hIncrement T x r s hT hx hr hrs (by linarith)
  have hIF : Integrable F ((independentBridgeLaw (Fin 3)).map rb) :=
    (integrable_map_measure hF.aestronglyMeasurable hb.aemeasurable).mpr hI.1
  have hscale := hIF.smul_measure (c := ENNReal.ofReal (8 * Real.exp M))
    ENNReal.ofReal_ne_top
  have hdom := positiveBridge_path_domination hBridge hPositive T x y (T / 2) M
    hT hx hy (by positivity) le_rfl hxy hM
  have hIP := hscale.mono_measure hdom
  constructor
  · exact (integrable_map_measure hF.aestronglyMeasurable hp.aemeasurable).mp hIP
  · have hle := integral_mono_measure hdom
      (Filter.Eventually.of_forall (fun f ↦ sq_nonneg
        (f ⟨s, hr.trans hrs, hs⟩ - f ⟨r, hr, hrs.trans hs⟩))) hscale
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
      integral_map hp.aemeasurable hF.aestronglyMeasurable,
      integral_map hb.aemeasurable hF.aestronglyMeasurable] at hle
    have hmul := mul_le_mul_of_nonneg_left hI.2 (by positivity : 0 ≤ 8 * Real.exp M)
    change (∫ ω, (positiveEndpointBridge T x y s ω -
      positiveEndpointBridge T x y r ω) ^ 2 ∂positiveBridgeCoefficientLaw T x y) ≤ _ at hle
    calc
      _ ≤ _ := hle
      _ ≤ _ := hmul
      _ = _ := by ring

end SRWTightness
