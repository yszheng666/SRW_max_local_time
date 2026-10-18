import SRWTightness.ConvexInnerCutoff

namespace SRWTightness

theorem convexInnerCutoff_continuous_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    Continuous (convexInnerCutoff K ε) ∧
      Continuous (fderiv ℝ (convexInnerCutoff K ε)) :=
  ⟨(convexInnerCutoff_differentiable K hclosed hconvex ε hε).continuous,
    (convexInnerCutoff_fderiv_lipschitz K hclosed hconvex ε hε).continuous⟩

theorem convexInnerCutoff_strict_superlevel_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Convex ℝ {x | t < convexInnerCutoff K ε x} := by
  classical
  by_cases hn : (convexErosion K ε).Nonempty
  · simpa only [convexInnerCutoff, if_pos hn] using
      convexOuterCutoff_strict_superlevel_convex _ hn (convexErosion_isComplete K hclosed ε)
        (convexErosion_convex K hconvex ε) ε hε t
  · by_cases ht : t < 0
    · simpa [convexInnerCutoff, hn, ht] using (convex_univ : Convex ℝ (Set.univ : Set E))
    · simpa [convexInnerCutoff, hn, ht] using (convex_empty : Convex ℝ (∅ : Set E))

/-- The constructed inner and outer smooth functions bracket the actual event indicator. -/
theorem convex_smoothing_indicator_envelope {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (x : E) :
    convexInnerCutoff K ε x ≤ K.indicator (fun _ ↦ (1 : ℝ)) x ∧
      K.indicator (fun _ ↦ (1 : ℝ)) x ≤ convexOuterCutoff K ε x := by
  classical
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    exact ⟨(convexInnerCutoff_bounds K ε x).2,
      (convexOuterCutoff_eq_one K ε hε x (Metric.infDist_zero_of_mem hx)).ge⟩
  · rw [Set.indicator_of_notMem hx, convexInnerCutoff_eq_zero K hclosed hconvex ε hε x hx]
    exact ⟨le_rfl, (convexOuterCutoff_bounds K ε x).1⟩

end SRWTightness
