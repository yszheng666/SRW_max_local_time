import SRWTightness.ConvexCutoffIntegrals

open MeasureTheory

namespace SRWTightness

/-- Inner smoothing loses at most the measure of the actual eroded boundary layer. -/
theorem convexInnerCutoff_boundary_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ μ.real K - (∫ x, convexInnerCutoff K ε x ∂μ) ∧
      μ.real K - (∫ x, convexInnerCutoff K ε x ∂μ) ≤
        μ.real (K \ convexErosion K ε) := by
  have hh := convexInnerCutoff_integral_bounds μ K hclosed hconvex ε hε
  rw [measureReal_sdiff (convexErosion_subset K ε hε.le)
    (convexErosion_isClosed K hclosed ε).measurableSet]
  constructor <;> linarith

/-- Outer smoothing gains at most the measure of the actual outer boundary layer. -/
theorem convexOuterCutoff_boundary_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hne : K.Nonempty)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ (∫ x, convexOuterCutoff K ε x ∂μ) - μ.real K ∧
      (∫ x, convexOuterCutoff K ε x ∂μ) - μ.real K ≤
        μ.real ({x | Metric.infDist x K < ε} \ K) := by
  have hh := convexOuterCutoff_integral_bounds μ K hne hclosed hconvex ε hε
  have hs : K ⊆ {x | Metric.infDist x K < ε} := by
    intro x hx
    change Metric.infDist x K < ε
    rw [Metric.infDist_zero_of_mem hx]
    exact hε
  rw [measureReal_sdiff hs hclosed.measurableSet]
  constructor <;> linarith

/-- Actual smooth expectation errors and actual target boundary masses control the convex event. -/
theorem convex_event_comparison_of_smoothing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ κ : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure κ]
    (K : Set E) (hne : K.Nonempty) (hclosed : IsClosed K) (hconvex : Convex ℝ K)
    (ε : ℝ) (hε : 0 < ε) (δ b : ℝ)
    (hlerror : |(∫ x, convexInnerCutoff K ε x ∂μ) -
      ∫ x, convexInnerCutoff K ε x ∂κ| ≤ δ)
    (huerror : |(∫ x, convexOuterCutoff K ε x ∂μ) -
      ∫ x, convexOuterCutoff K ε x ∂κ| ≤ δ)
    (hlboundary : κ.real (K \ convexErosion K ε) ≤ b)
    (huboundary : κ.real ({x | Metric.infDist x K < ε} \ K) ≤ b) :
    |μ.real K - κ.real K| ≤ δ + b := by
  exact event_smoothing_comparison μ κ K hclosed.measurableSet
    (convexInnerCutoff K ε) (convexOuterCutoff K ε)
    (convexInnerCutoff_integrable μ K hclosed hconvex ε hε)
    (convexOuterCutoff_integrable μ K hne hclosed hconvex ε hε)
    (convex_smoothing_indicator_envelope K hclosed hconvex ε hε) δ b hlerror huerror
    ((convexInnerCutoff_boundary_error κ K hclosed hconvex ε hε).2.trans hlboundary)
    ((convexOuterCutoff_boundary_error κ K hne hclosed hconvex ε hε).2.trans huboundary)

end SRWTightness
