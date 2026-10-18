import SRWTightness.OccupationLaplaceSupport

open MeasureTheory ProbabilityTheory

namespace SRWTightness

 theorem kernel_event_probability_le_one {X Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Z] (κ : Kernel X Z) [IsMarkovKernel κ] (s : Set Z) (x : X) :
    (κ x).real s ≤ 1 :=
  (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)).trans_eq (by simp)

 theorem integrable_kernel_event_probability {X Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Z] (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X Z) [IsMarkovKernel κ] (s : Set Z) (hs : MeasurableSet s) :
    Integrable (fun x ↦ (κ x).real s) μ := by
  refine ⟨(κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact kernel_event_probability_le_one κ s x)

 theorem measure_comp_real_event {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) [IsFiniteMeasure μ] (κ : Kernel X Z) [IsMarkovKernel κ]
    (s : Set Z) (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s = ∫ x, (κ x).real s ∂μ := by
  rw [← integral_indicator_one hs]
  rw [integral_kernel_comp_real μ κ (s.indicator (1 : Z → ℝ))
    ((integrable_const _).indicator hs)]
  simp_rw [integral_indicator_one hs]

end SRWTightness
