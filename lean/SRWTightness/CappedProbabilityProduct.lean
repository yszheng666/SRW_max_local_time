import SRWTightness.CappedProductIntegral

open MeasureTheory
namespace SRWTightness

/-- Under a probability law, a uniform capped product bound also bounds its capped integral. -/
theorem capped_probability_product_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℕ) (cap : ℕ)
    (p q : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hbound : ∀ k l, k ≤ cap → l ≤ cap → p k * q l ≤ K) :
    (∫ ω, {u | X u ≤ cap ∧ Y u ≤ cap}.indicator
      (fun u ↦ p (X u) * q (Y u)) ω ∂μ) ≤ K := by
  have hh := capped_product_integral_upper_bound μ Set.univ X Y cap p q
    (fun _ ↦ 1) K MeasurableSet.univ (integrable_const 1) hK hp hq
    (fun _ ↦ zero_le_one) (fun ω hx hy ↦ by simpa using hbound (X ω) (Y ω) hx hy)
  simpa using hh

end SRWTightness
