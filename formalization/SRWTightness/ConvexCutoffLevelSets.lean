import SRWTightness.ConvexOuterGradient
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace SRWTightness

theorem quadraticCutoff_antitone : Antitone quadraticCutoff := by
  apply antitone_of_deriv_nonpos (fun x ↦ (quadraticCutoff_hasDerivAt x).differentiableAt)
  intro x
  rw [quadraticCutoff_deriv]
  exact (quadraticCutoffSlope_bounds x).2

theorem scaledQuadraticCutoff_antitone (ε : ℝ) (hε : 0 < ε) :
    Antitone (scaledQuadraticCutoff ε) := by
  intro x y hxy
  exact quadraticCutoff_antitone (div_le_div_of_nonneg_right hxy hε.le)

/-- Metric distance to a nonempty complete convex set is a convex function. -/
theorem convexDistance_convexOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) : ConvexOn ℝ Set.univ (fun x ↦ Metric.infDist x K) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let p := convexNearestPoint K hne hcomplete hconvex x
  let q := convexNearestPoint K hne hcomplete hconvex y
  have hp : p ∈ K := convexNearestPoint_mem K hne hcomplete hconvex x
  have hq : q ∈ K := convexNearestPoint_mem K hne hcomplete hconvex y
  have hm := Metric.infDist_le_dist_of_mem (x := a • x + b • y)
    (hconvex hp hq ha hb hab)
  have he : a • x + b • y - (a • p + b • q) = a • (x - p) + b • (y - q) := by
    simp only [smul_sub]
    abel
  rw [dist_eq_norm, he] at hm
  have ht := norm_add_le (a • (x - p)) (b • (y - q))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb] at ht
  simpa only [convexNearestPoint_infDist K hne hcomplete hconvex, smul_eq_mul, p, q]
    using hm.trans ht

/-- Every non-strict upper level set of the outer cutoff is convex. -/
theorem convexOuterCutoff_superlevel_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Convex ℝ {x | t ≤ convexOuterCutoff K ε x} := by
  intro x hx y hy a b ha hb hab
  have hd := (convexDistance_convexOn K hne hcomplete hconvex).2
    (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hd
  have hm : a * Metric.infDist x K + b * Metric.infDist y K ≤
      max (Metric.infDist x K) (Metric.infDist y K) := by
    calc
      _ ≤ a * max (Metric.infDist x K) (Metric.infDist y K) +
          b * max (Metric.infDist x K) (Metric.infDist y K) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  have hf := scaledQuadraticCutoff_antitone ε hε (hd.trans hm)
  rcases le_total (Metric.infDist x K) (Metric.infDist y K) with h | h
  · rw [max_eq_right h] at hf
    exact hy.trans hf
  · rw [max_eq_left h] at hf
    exact hx.trans hf

/-- Every strict upper level set of the outer cutoff is convex. -/
theorem convexOuterCutoff_strict_superlevel_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Convex ℝ {x | t < convexOuterCutoff K ε x} := by
  intro x hx y hy a b ha hb hab
  have hd := (convexDistance_convexOn K hne hcomplete hconvex).2
    (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hd
  have hm : a * Metric.infDist x K + b * Metric.infDist y K ≤
      max (Metric.infDist x K) (Metric.infDist y K) := by
    calc
      _ ≤ a * max (Metric.infDist x K) (Metric.infDist y K) +
          b * max (Metric.infDist x K) (Metric.infDist y K) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  have hf := scaledQuadraticCutoff_antitone ε hε (hd.trans hm)
  rcases le_total (Metric.infDist x K) (Metric.infDist y K) with h | h
  · rw [max_eq_right h] at hf
    exact hy.trans_le hf
  · rw [max_eq_left h] at hf
    exact hx.trans_le hf

end SRWTightness
