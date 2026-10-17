import SRWTightness.MarkedGWLeafIntegral
import SRWTightness.EarlyGWPopulationIntegral

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Conditional mark moments and the GW marginal give a complete capped tree-moment bound. -/
theorem markedGWJoint_early_endpoint_bound {M : Type*} [Countable M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (hinput : MarkedGWJointInput M)
    (hGW : GeometricGWOneRootMarginalInput) (μ : Measure M) (hμ : IsProbabilityMeasure μ)
    (j : ℕ) (hj : 1 ≤ j) [MeasurableSpace (FiniteExcursionRecord M j)]
    [MeasurableSingletonClass (FiniteExcursionRecord M j)]
    (b e : ℝ) (hb : 0 < b) (hbd : b ≤ 4 * ((j : ℝ) + 1))
    (s : Set GeometricGWRecord) (hs : ∀ r ∈ s, geometricGWHeight r j ≤ b)
    (f : List M → ℝ≥0∞)
    (hf : ∀ k : ℕ, Real.sqrt (2 * (k : ℝ)) ≤ b →
      (∫⁻ rs, f rs ∂independentForestLaw μ k) ≤
        ENNReal.ofReal (Real.exp (2 * b + 4 * (k : ℝ) / b + e))) :
    (∫⁻ r in {r | finiteRecordPopulationList j r ∈ s},
      f (finiteRecordLeaves j r) ∂finiteRecordReferenceMeasure μ j) ≤
        ENNReal.ofReal (36 * (j : ℝ) ^ 2 *
          Real.exp (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) + e)) := by
  rw [markedGWJoint_leaf_lintegral hinput μ hμ j s f]
  apply le_trans _ (early_gw_population_lintegral hGW j hj b e hb hbd s hs)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem s.to_countable.measurableSet] with g hg
  exact hf (geometricGWPopulation g j) (hs g hg)

end SRWTightness
