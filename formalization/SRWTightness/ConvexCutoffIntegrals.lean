import SRWTightness.ConvexSmoothingEnvelope
import SRWTightness.EventSmoothingComparison
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory

namespace SRWTightness

theorem convexInnerCutoff_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    Integrable (convexInnerCutoff K ε) μ := by
  apply Integrable.of_bound
    (convexInnerCutoff_continuous_fderiv K hclosed hconvex ε hε).1.aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (convexInnerCutoff_bounds K ε x).1]
  exact (convexInnerCutoff_bounds K ε x).2

theorem convexOuterCutoff_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    Integrable (convexOuterCutoff K ε) μ := by
  apply Integrable.of_bound
    (convexOuterCutoff_continuous_fderiv K hne hclosed.isComplete hconvex ε hε).1.aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (convexOuterCutoff_bounds K ε x).1]
  exact (convexOuterCutoff_bounds K ε x).2

/-- The inner smooth expectation lies between the erosion mass and the original event mass. -/
theorem convexInnerCutoff_integral_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    μ.real (convexErosion K ε) ≤ ∫ x, convexInnerCutoff K ε x ∂μ ∧
      (∫ x, convexInnerCutoff K ε x ∂μ) ≤ μ.real K := by
  classical
  have hi := convexInnerCutoff_integrable μ K hclosed hconvex ε hε
  have he := (convexErosion_isClosed K hclosed ε).measurableSet
  have hiE : Integrable ((convexErosion K ε).indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator he
  have hiK : Integrable (K.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator hclosed.measurableSet
  constructor
  · rw [← integral_indicator_one he]
    apply integral_mono hiE hi
    intro x
    by_cases hx : x ∈ convexErosion K ε
    · rw [Set.indicator_of_mem hx, convexInnerCutoff_eq_one K ε hε x hx]
    · rw [Set.indicator_of_notMem hx]
      exact (convexInnerCutoff_bounds K ε x).1
  · rw [← integral_indicator_one hclosed.measurableSet]
    exact integral_mono hi hiK (fun x ↦
      (convex_smoothing_indicator_envelope K hclosed hconvex ε hε x).1)

/-- The outer smooth expectation lies between the event mass and its open distance neighborhood. -/
theorem convexOuterCutoff_integral_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    μ.real K ≤ ∫ x, convexOuterCutoff K ε x ∂μ ∧
      (∫ x, convexOuterCutoff K ε x ∂μ) ≤ μ.real {x | Metric.infDist x K < ε} := by
  classical
  have hi := convexOuterCutoff_integrable μ K hne hclosed hconvex ε hε
  have ht : MeasurableSet {x | Metric.infDist x K < ε} :=
    (isOpen_lt (Metric.continuous_infDist_pt K) continuous_const).measurableSet
  have hiT : Integrable ({x | Metric.infDist x K < ε}.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator ht
  have hiK : Integrable (K.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator hclosed.measurableSet
  constructor
  · rw [← integral_indicator_one hclosed.measurableSet]
    exact integral_mono hiK hi (fun x ↦
      (convex_smoothing_indicator_envelope K hclosed hconvex ε hε x).2)
  · rw [← integral_indicator_one ht]
    apply integral_mono hi hiT
    intro x
    by_cases hx : x ∈ {z | Metric.infDist z K < ε}
    · rw [Set.indicator_of_mem hx]
      exact (convexOuterCutoff_bounds K ε x).2
    · rw [Set.indicator_of_notMem hx, convexOuterCutoff_eq_zero K ε hε x (le_of_not_gt hx)]

end SRWTightness
