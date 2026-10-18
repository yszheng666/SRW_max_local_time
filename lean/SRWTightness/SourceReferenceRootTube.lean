import SRWTightness.SourceRootGWHorizon
import SRWTightness.SourceProfileReferenceMeasure

open MeasureTheory Filter

namespace SRWTightness

/-- The GW lower tube estimate applies to the actual source-profile marked reference tree. -/
theorem source_reference_root_tube_probability (hGW : GWBarrierLowerInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b : Site) (a : ℝ) (K : Finset Site), 1 ≤ a →
      a ≤ sourceLowerRadius t / t ^ 6 → K ⊆ translateFinset b (diskFinset a) →
      MarkedGWTreeInput (Mark K) →
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) n)]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) n)],
      let μ := finiteRecordReferenceMeasure
        (referenceMarkLaw
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
          (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let y := sourceTerminalRoot t q + 1 / 4
        c * gwBarrierPrefactor n (Real.sqrt 2) y 4 (sourceGWLowerEndpoint t) *
            min (Real.sqrt (Real.sqrt 2 / (y * n))) 1 ≤
          μ.real {r | finiteRecordPopulationList n r ∈ sourceGWLowerTubeEvent t n q} := by
  obtain ⟨c, hc, hh⟩ := source_root_gw_lower_tube_probability hGW
  refine ⟨c, hc, ?_⟩
  filter_upwards [hh, eventually_ge_atTop sourceCapacityHalfThreshold] with t ht htcap
  intro b a K ha hcut hK hmarked
  dsimp only
  intro inst₁ inst₂
  intro q hqlo hqhi
  have hpop := (source_profile_reference_measure b t a K hmarked htcap ha hcut hK
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1)).2
    (sourceGWLowerTubeEvent t (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) q)
  simp only [measureReal_def, hpop]
  exact ht q hqlo hqhi

end SRWTightness
