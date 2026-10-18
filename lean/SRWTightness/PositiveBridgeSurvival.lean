import SRWTightness.PositiveBridgeFullCurve

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Positive endpoints make the actual flat conditioning event have nonzero probability. -/
theorem positiveBridge_probability (hReflection : BridgeReflectionInput)
    (T x y : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) :
    IsProbabilityMeasure (positiveBridgeCoefficientLaw T x y) := by
  have hf := hReflection T (x - y) x hT hx (by linarith)
  have he : x - (x - y) = y := by ring
  rw [he] at hf
  have hp : 0 < gaussianCoefficientLaw.real (bridgeFlatEvent T (x - y) x) := by
    rw [hf]
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    have h : 0 < 2 * x * y / T := by positivity
    linarith
  have hn : gaussianCoefficientLaw (bridgeFlatEvent T (x - y) x) ≠ 0 := by
    intro h
    simp [Measure.real, h] at hp
  exact cond_isProbabilityMeasure hn

/-- Full-time crossings are measurable up to a null set under the conditioned bridge. -/
theorem positiveBridge_crossing_nullMeasurable (T x y s : ℝ) (bound : ℝ → ℝ)
    (hb : Continuous bound) :
    NullMeasurableSet
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, positiveEndpointBridge T x y t ω < bound t}
      (positiveBridgeCoefficientLaw T x y) := by
  refine ⟨(fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y t ω) ⁻¹'
      dyadicLowerPathEvent s bound,
    (dyadicLowerPathEvent_measurable s bound).preimage
      (positiveEndpointBridge_path_measurable T x y s), ?_⟩
  filter_upwards [positiveEndpointBridge_ae_continuous T x y] with ω hω
  exact propext (continuous_crossing_iff_dyadic _ bound hω hb s)

/-- Survival is exactly one minus the full-time crossing probability. -/
theorem positiveBridge_survival_real (hReflection : BridgeReflectionInput)
    (T x y s : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y)
    (bound : ℝ → ℝ) (hb : Continuous bound) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) s, bound t ≤ positiveEndpointBridge T x y t ω} =
      1 - (positiveBridgeCoefficientLaw T x y).real
        {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, positiveEndpointBridge T x y t ω < bound t} := by
  letI := positiveBridge_probability hReflection T x y hT hx hy
  have he : {ω | ∀ t ∈ Set.Icc (0 : ℝ) s, bound t ≤ positiveEndpointBridge T x y t ω} =
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, positiveEndpointBridge T x y t ω < bound t}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  rw [he]
  exact probReal_compl_eq_one_sub₀ (positiveBridge_crossing_nullMeasurable T x y s bound hb)

end SRWTightness
