import SRWTightness.ConvexErosion
import SRWTightness.ConvexCutoffLevelSets

namespace SRWTightness

/-- Smooth from the eroded set, with the zero function when the erosion is empty. -/
noncomputable def convexInnerCutoff {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (ε : ℝ) (x : E) : ℝ := by
  classical
  exact if (convexErosion K ε).Nonempty then convexOuterCutoff (convexErosion K ε) ε x else 0

theorem convexInnerCutoff_of_nonempty {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (ε : ℝ) (hn : (convexErosion K ε).Nonempty) :
    convexInnerCutoff K ε = convexOuterCutoff (convexErosion K ε) ε := by
  funext x
  simp only [convexInnerCutoff, if_pos hn]

theorem convexInnerCutoff_of_empty {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (ε : ℝ) (hn : ¬ (convexErosion K ε).Nonempty) :
    convexInnerCutoff K ε = fun _ ↦ 0 := by
  funext x
  simp only [convexInnerCutoff, if_neg hn]

theorem convexInnerCutoff_bounds {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (ε : ℝ) (x : E) :
    0 ≤ convexInnerCutoff K ε x ∧ convexInnerCutoff K ε x ≤ 1 := by
  classical
  unfold convexInnerCutoff
  split_ifs
  · exact convexOuterCutoff_bounds _ _ _
  · constructor <;> norm_num

theorem convexInnerCutoff_eq_one {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : x ∈ convexErosion K ε) :
    convexInnerCutoff K ε x = 1 := by
  classical
  rw [convexInnerCutoff, if_pos ⟨x, hx⟩]
  exact convexOuterCutoff_eq_one _ ε hε x (Metric.infDist_zero_of_mem hx)

theorem convexInnerCutoff_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : x ∉ K) :
    convexInnerCutoff K ε x = 0 := by
  classical
  unfold convexInnerCutoff
  split_ifs with hne
  · apply convexOuterCutoff_eq_zero _ ε hε x
    have hc := convexErosion_isComplete K hclosed ε
    have hv := convexErosion_convex K hconvex ε
    let p := convexNearestPoint (convexErosion K ε) hne hc hv x
    have hp : p ∈ convexErosion K ε := convexNearestPoint_mem _ hne hc hv x
    have hd : Metric.infDist x (convexErosion K ε) = ‖x - p‖ :=
      convexNearestPoint_infDist _ hne hc hv x
    rw [hd]
    exact le_of_not_gt (fun hh ↦ hx (convexErosion_near_mem K ε p x hp hh.le))
  · rfl

theorem convexInnerCutoff_differentiable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    Differentiable ℝ (convexInnerCutoff K ε) := by
  classical
  by_cases hn : (convexErosion K ε).Nonempty
  · have he : convexInnerCutoff K ε = convexOuterCutoff (convexErosion K ε) ε := by
      funext x
      simp only [convexInnerCutoff, if_pos hn]
    rw [he]
    exact fun x ↦ (convexOuterCutoff_hasFDerivAt _ hn (convexErosion_isComplete K hclosed ε)
      (convexErosion_convex K hconvex ε) ε hε x).differentiableAt
  · have he : convexInnerCutoff K ε = fun _ ↦ 0 := by
      funext x
      simp only [convexInnerCutoff, if_neg hn]
    rw [he]
    exact differentiable_const 0

theorem convexInnerCutoff_fderiv_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ (convexInnerCutoff K ε) x‖ ≤ 2 / ε := by
  classical
  by_cases hn : (convexErosion K ε).Nonempty
  · rw [convexInnerCutoff_of_nonempty K ε hn]
    exact convexOuterCutoff_fderiv_bound _ hn (convexErosion_isComplete K hclosed ε)
        (convexErosion_convex K hconvex ε) ε hε x
  · rw [convexInnerCutoff_of_empty K ε hn]
    simp only [fderiv_const_apply, norm_zero]
    positivity

theorem convexInnerCutoff_fderiv_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith ⟨8 / ε ^ 2, by positivity⟩ (fderiv ℝ (convexInnerCutoff K ε)) := by
  classical
  by_cases hn : (convexErosion K ε).Nonempty
  · rw [convexInnerCutoff_of_nonempty K ε hn]
    exact convexOuterCutoff_fderiv_lipschitz _ hn (convexErosion_isComplete K hclosed ε)
        (convexErosion_convex K hconvex ε) ε hε
  · rw [convexInnerCutoff_of_empty K ε hn]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [fderiv_const_apply, dist_self]
    positivity

theorem convexInnerCutoff_superlevel_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Convex ℝ {x | t ≤ convexInnerCutoff K ε x} := by
  classical
  by_cases hn : (convexErosion K ε).Nonempty
  · simpa only [convexInnerCutoff, if_pos hn] using
      convexOuterCutoff_superlevel_convex _ hn (convexErosion_isComplete K hclosed ε)
        (convexErosion_convex K hconvex ε) ε hε t
  · by_cases ht : t ≤ 0
    · simpa [convexInnerCutoff, hn, ht] using (convex_univ : Convex ℝ (Set.univ : Set E))
    · simpa [convexInnerCutoff, hn, ht] using (convex_empty : Convex ℝ (∅ : Set E))

end SRWTightness
