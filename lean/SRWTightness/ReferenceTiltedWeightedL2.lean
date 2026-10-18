import SRWTightness.ReferenceTiltedCovarianceDerivative

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace SRWTightness

/-- Actual probability-weighted mark observations remain square integrable under small tilts. -/
theorem referenceMark_tilted_weighted_memLp_two (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) :
    MemLp (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)) 2
      ((referenceMarkLaw D K α).tilted (fun Y ↦ s * ∑ z, β z * (Y z : ℝ))) := by
  let μ := referenceMarkLaw D K α
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  have hmH : Measurable H := by dsimp [H]; fun_prop
  have hmX : Measurable X := by dsimp [X]; fun_prop
  have hH2 : MemLp (fun Y ↦ H Y ^ 2) 2 μ := by
    simpa only [pow_two] using
      referenceMark_weighted_product_memLp_two D K hKD α hα hcap w w hw hw hw1 hw1 L hL hG
  have ht := referenceMark_linear_exp_interior D K hKD α hα hcap β L hL hG s
    (hs.trans (one_div_lt_one_div_of_lt (by positivity) (by linarith)))
  have ht2 := referenceMark_doubled_exp_interior D K hKD α hα hcap β L hL hG s hs
  have htH := weighted_exponential_interior μ (fun Y ↦ H Y ^ 2) X (hmH.pow_const 2)
    (fun Y ↦ sq_nonneg _) hH2 hmX s ht2
  have hi := weighted_tilted_pow_integrable μ (fun Y ↦ H Y ^ 2) X
    (hmH.pow_const 2) (fun Y ↦ sq_nonneg _) s ht htH 0
  apply (memLp_two_iff_integrable_sq hmH.aestronglyMeasurable).mpr
  simpa only [pow_zero, mul_one] using hi

end SRWTightness
