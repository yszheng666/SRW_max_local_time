import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
namespace SRWTightness

/-- A nonnegative capped product may be bounded and uncapped inside an integrable envelope.
No independence is required between the two integer-valued coordinates. -/
theorem capped_product_integral_upper_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (X Y : Ω → ℕ) (cap : ℕ) (p q : ℕ → ℝ)
    (f : Ω → ℝ) (K : ℝ) (hS : MeasurableSet S) (hf : Integrable f μ)
    (hK : 0 ≤ K) (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hf0 : ∀ ω, 0 ≤ f ω)
    (hbound : ∀ ω, X ω ≤ cap → Y ω ≤ cap → p (X ω) * q (Y ω) ≤ K * f ω) :
    (∫ ω, {u | u ∈ S ∧ X u ≤ cap ∧ Y u ≤ cap}.indicator
      (fun u ↦ p (X u) * q (Y u)) ω ∂μ) ≤ K * ∫ ω, S.indicator f ω ∂μ := by
  classical
  have hnonneg : ∀ ω, 0 ≤ {u | u ∈ S ∧ X u ≤ cap ∧ Y u ≤ cap}.indicator
      (fun u ↦ p (X u) * q (Y u)) ω := by
    intro ω
    by_cases h : ω ∈ {u | u ∈ S ∧ X u ≤ cap ∧ Y u ≤ cap}
    · simpa only [Set.indicator_of_mem h] using mul_nonneg (hp (X ω)) (hq (Y ω))
    · simp only [Set.indicator_of_notMem h, le_refl]
  have hpoint : ∀ ω, {u | u ∈ S ∧ X u ≤ cap ∧ Y u ≤ cap}.indicator
      (fun u ↦ p (X u) * q (Y u)) ω ≤ K * S.indicator f ω := by
    intro ω
    by_cases hs : ω ∈ S
    · rw [Set.indicator_of_mem hs]
      by_cases hc : X ω ≤ cap ∧ Y ω ≤ cap
      · rw [Set.indicator_of_mem (show ω ∈ {u | u ∈ S ∧ X u ≤ cap ∧ Y u ≤ cap}
          from ⟨hs, hc⟩)]
        exact hbound ω hc.1 hc.2
      · rw [Set.indicator_of_notMem (show ω ∉ {u | u ∈ S ∧ X u ≤ cap ∧ Y u ≤ cap}
          from fun h ↦ hc h.2)]
        exact mul_nonneg hK (hf0 ω)
    · simp only [Set.indicator_of_notMem hs,
        Set.indicator_of_notMem (show ω ∉ {u | u ∈ S ∧ X u ≤ cap ∧ Y u ≤ cap}
          from fun h ↦ hs h.1), mul_zero, le_refl]
  calc
    _ ≤ ∫ ω, K * S.indicator f ω ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall hnonneg)
        ((hf.indicator hS).const_mul K) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul K _

end SRWTightness
