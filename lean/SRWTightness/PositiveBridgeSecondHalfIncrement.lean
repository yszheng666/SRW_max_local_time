import SRWTightness.PositiveBridgeIncrement

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Time reversal transfers the first-half second moment to every interval in the second half. -/
theorem positiveBridge_second_half_increment (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hIncrement : BesselThreeIncrementInput) (T x y M r s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hy : 0 < y)
    (hr : T / 2 ≤ r) (hrs : r ≤ s) (hs : s ≤ T)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    Integrable (fun ω ↦
      (positiveEndpointBridge T x y s ω - positiveEndpointBridge T x y r ω) ^ 2)
      (positiveBridgeCoefficientLaw T x y) ∧
    (∫ ω, (positiveEndpointBridge T x y s ω - positiveEndpointBridge T x y r ω) ^ 2
      ∂positiveBridgeCoefficientLaw T x y) ≤ 24 * Real.exp M * (s - r) := by
  have hI := positiveBridge_first_half_increment hBridge hPositive hIncrement
    T y x M (T - s) (T - r) hT hy hx (by linarith) (by linarith) (by linarith)
    (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hxy)
    (by simpa only [sub_sq_comm] using hM)
  let F : (Set.Icc (0 : ℝ) T → ℝ) → ℝ := fun f ↦
    (f ⟨T - r, by constructor <;> linarith⟩ -
      f ⟨T - s, by constructor <;> linarith⟩) ^ 2
  have hF : Measurable F := by
    exact ((measurable_pi_apply (⟨T - r, by constructor <;> linarith⟩ : Set.Icc (0 : ℝ) T)).sub
      (measurable_pi_apply (⟨T - s, by constructor <;> linarith⟩ : Set.Icc (0 : ℝ) T))).pow_const 2
  have hp : Measurable (fun ω (t : Set.Icc (0 : ℝ) T) ↦
      positiveEndpointBridge T x y (T - t) ω) :=
    measurable_pi_iff.mpr (fun t ↦ positiveEndpointBridge_measurable T x y _)
  have hb := positiveEndpointBridge_path_measurable T y x T
  have he : (fun ω ↦ F (fun t : Set.Icc (0 : ℝ) T ↦
      positiveEndpointBridge T x y (T - t) ω)) =
      (fun ω ↦ (positiveEndpointBridge T x y s ω -
        positiveEndpointBridge T x y r ω) ^ 2) := by
    funext ω
    dsimp [F]
    rw [sub_sub_cancel, sub_sub_cancel, sub_sq_comm]
  have hIF : Integrable F ((positiveBridgeCoefficientLaw T y x).map
      (fun ω (t : Set.Icc (0 : ℝ) T) ↦ positiveEndpointBridge T y x t ω)) :=
    (integrable_map_measure hF.aestronglyMeasurable hb.aemeasurable).mpr hI.1
  rw [← hReverse T x y hT hx hy] at hIF
  constructor
  · have hi := (integrable_map_measure hF.aestronglyMeasurable hp.aemeasurable).mp hIF
    simp only [Function.comp_def] at hi
    rw [he] at hi
    exact hi
  · have hh := congrArg (fun μ ↦ ∫ f, F f ∂μ) (hReverse T x y hT hx hy)
    rw [integral_map hp.aemeasurable hF.aestronglyMeasurable,
      integral_map hb.aemeasurable hF.aestronglyMeasurable] at hh
    rw [he] at hh
    rw [hh]
    exact hI.2.trans_eq (by ring)

end SRWTightness
