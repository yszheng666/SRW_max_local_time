import SRWTightness.MarkedGWLeafIntegral

open MeasureTheory
open scoped ENNReal BigOperators

namespace SRWTightness

/-- Joint root weights on an independent mark list equal the fixed-size product-law test. -/
theorem independentForest_joint_root_lintegral {M : Type*} [Countable M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) (k : ℕ)
    (N₁ N₂ : M → ℕ) (H : ℕ × ℕ → ℝ≥0∞) :
    (∫⁻ rs, H ((rs.map N₁).sum, (rs.map N₂).sum) ∂independentForestLaw μ k) =
      ∫⁻ v : Fin k → M, H (∑ i, N₁ (v i), ∑ i, N₂ (v i)) ∂Measure.pi (fun _ ↦ μ) := by
  rw [independentForestLaw, lintegral_map (measurable_of_countable _)
    (measurable_of_countable _)]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

end SRWTightness
