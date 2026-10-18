import SRWTightness.PositiveBridgeSurvival

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Continuous paths turn the full-time survival test into a countable test up to null sets. -/
theorem continuousPath_survival_nullMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℝ → Ω → ℝ) (hm : ∀ t, Measurable (f t))
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ f t ω))
    (s : ℝ) (bound : ℝ → ℝ) (hb : Continuous bound) :
    NullMeasurableSet {ω | ∀ t ∈ Set.Icc (0 : ℝ) s, bound t ≤ f t ω} μ := by
  have hn : NullMeasurableSet
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, f t ω < bound t} μ := by
    refine ⟨(fun ω (t : Set.Icc (0 : ℝ) s) ↦ f t ω) ⁻¹'
      dyadicLowerPathEvent s bound,
      (dyadicLowerPathEvent_measurable s bound).preimage
        (measurable_pi_iff.mpr (fun t ↦ hm t)), ?_⟩
    filter_upwards [hc] with ω hω
    exact propext (continuous_crossing_iff_dyadic _ bound hω hb s)
  have he : {ω | ∀ t ∈ Set.Icc (0 : ℝ) s, bound t ≤ f t ω} =
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) s, f t ω < bound t}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  rw [he]
  exact hn.compl

/-- The actual flat barrier is measurable in the completion of the coefficient law. -/
theorem bridgeFlatEvent_nullMeasurable (T b q : ℝ) :
    NullMeasurableSet (bridgeFlatEvent T b q) gaussianCoefficientLaw := by
  have hm : ∀ t, Measurable (fun ω ↦ -endpointBrownianBridge T b t ω) := by
    intro t
    exact ((actualIntervalBridge_measurable T t).add measurable_const).neg
  have hc : ∀ᵐ ω ∂gaussianCoefficientLaw,
      Continuous (fun t ↦ -endpointBrownianBridge T b t ω) := by
    filter_upwards [actualIntervalBridge_continuous T] with ω hω
    exact (hω.add ((continuous_id.div_const T).mul continuous_const)).neg
  simpa only [bridgeFlatEvent, neg_le_neg_iff] using
    continuousPath_survival_nullMeasurable gaussianCoefficientLaw _ hm hc T
      (fun _ ↦ -q) continuous_const

/-- Multiplying a conditional probability by its positive conditioning mass recovers a subevent. -/
theorem conditional_real_mul_of_subset {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s t : Set Ω)
    (hs : NullMeasurableSet s μ) (hpos : 0 < μ.real s) (hts : t ⊆ s) :
    (ProbabilityTheory.cond μ s).real t * μ.real s = μ.real t := by
  have he : t ∩ s = t := Set.inter_eq_left.mpr hts
  have hc : (ProbabilityTheory.cond μ s).real t = (μ.real s)⁻¹ * μ.real t := by
    simp only [ProbabilityTheory.cond, Measure.real, Measure.smul_apply,
      smul_eq_mul, Measure.restrict_apply₀' hs, he, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
  rw [hc]
  field_simp

end SRWTightness
