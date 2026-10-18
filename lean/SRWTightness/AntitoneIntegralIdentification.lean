import SRWTightness.IntegralStrictOfAEStrict
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory
namespace SRWTightness

/-- An antitone function is determined pointwise by its prefix integrals against a
continuous one. -/
theorem antitone_eq_of_prefix_integrals (μ : Measure ℝ)
    (hpos : ∀ a b : ℝ, a < b → 0 < μ (Set.Ioc a b))
    (f g : ℝ → ℝ) (q : ℝ) (hfmono : Antitone f)
    (hgc : ∀ x < q, ContinuousAt g x)
    (hfi : ∀ b < q, IntegrableOn f (Set.Iic b) μ)
    (hgi : ∀ b < q, IntegrableOn g (Set.Iic b) μ)
    (he : ∀ b < q, (∫ x in Set.Iic b, f x ∂μ) = ∫ x in Set.Iic b, g x ∂μ) :
    ∀ x < q, f x = g x := by
  have hI (a b : ℝ) (hab : a ≤ b) (hbq : b < q) :
      (∫ x in Set.Ioc a b, f x ∂μ) = ∫ x in Set.Ioc a b, g x ∂μ := by
    have haq := hab.trans_lt hbq
    rw [← intervalIntegral.integral_of_le hab,
      ← intervalIntegral.integral_Iic_sub_Iic (hfi a haq) (hfi b hbq),
      he a haq, he b hbq,
      intervalIntegral.integral_Iic_sub_Iic (hgi a haq) (hgi b hbq),
      intervalIntegral.integral_of_le hab]
  intro x hx
  apply le_antisymm
  · by_contra hn
    have hgap : 0 < (f x - g x) / 2 := by linarith
    obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hgc x hx) _ hgap
    let a := x - δ / 2
    have hax : a < x := by dsimp [a]; linarith
    have hlt : ∀ᵐ y ∂μ.restrict (Set.Ioc a x), g y < f y := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      have hd : dist y x < δ := by
        rw [Real.dist_eq]
        apply abs_lt.mpr
        dsimp [a] at hy
        constructor <;> linarith [hy.1, hy.2]
      have hs := abs_lt.mp (show |g y - g x| < (f x - g x) / 2 from hnear hd)
      have hm := hfmono hy.2
      linarith [hs.2]
    have hp : 0 < (μ.restrict (Set.Ioc a x)) Set.univ := by
      simpa only [Measure.restrict_apply_univ] using hpos a x hax
    have hi := integral_strict_of_ae_strict (μ.restrict (Set.Ioc a x)) hp g f
      ((hgi x hx).mono_set (fun _ h ↦ h.2))
      ((hfi x hx).mono_set (fun _ h ↦ h.2)) hlt
    rw [hI a x hax.le hx] at hi
    exact (lt_irrefl _) hi
  · by_contra hn
    have hgap : 0 < (g x - f x) / 2 := by linarith
    obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hgc x hx) _ hgap
    let r := min (δ / 2) ((q - x) / 2)
    have hr : 0 < r := lt_min (by linarith) (by linarith)
    have hrd : r ≤ δ / 2 := min_le_left _ _
    have hrq : r ≤ (q - x) / 2 := min_le_right _ _
    have hxb : x < x + r := by linarith
    have hbq : x + r < q := by linarith
    have hlt : ∀ᵐ y ∂μ.restrict (Set.Ioc x (x + r)), f y < g y := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      have hd : dist y x < δ := by
        rw [Real.dist_eq]
        apply abs_lt.mpr
        constructor <;> linarith [hy.1, hy.2]
      have hs := abs_lt.mp (show |g y - g x| < (g x - f x) / 2 from hnear hd)
      have hm := hfmono hy.1.le
      linarith [hs.1]
    have hp : 0 < (μ.restrict (Set.Ioc x (x + r))) Set.univ := by
      simpa only [Measure.restrict_apply_univ] using hpos x (x + r) hxb
    have hi := integral_strict_of_ae_strict (μ.restrict (Set.Ioc x (x + r))) hp f g
      ((hfi (x + r) hbq).mono_set (fun _ h ↦ h.2))
      ((hgi (x + r) hbq).mono_set (fun _ h ↦ h.2)) hlt
    rw [hI x (x + r) hxb.le hbq] at hi
    exact (lt_irrefl _) hi

end SRWTightness
