import SRWTightness.SourceWalkSuccessIdentification

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- The original continuous success event is measurable up to a null set of the product law. -/
theorem source_local_time_success_nullMeasurable :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b : Site) (I : ℕ)
      (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      0 ≤ γ → 1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      NullMeasurableSet (sourceLocalTimeSuccessEvent t A γ b I z)
        (pathLaw.prod (independentBridgeLaw ℕ)) := by
  filter_upwards [source_walk_success_identification] with t ht
  intro A γ b I z hγ ha hcut hblo hbhi
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
  letI : MeasurableSpace (List (Mark K)) := ⊤
  letI : MeasurableSingletonClass (List (Mark K)) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (List (FiniteExcursionRecord (Mark K) n)) := ⊤
  letI : MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) n)) :=
    ⟨fun _ ↦ trivial⟩
  let E : Set (Sample × (ℕ → GaussianCoefficientSpace)) :=
    (fun p ↦ (sourceActualForest t b K p.1, p.2)) ⁻¹'
      sourceCoarseTerminalForestEvent t A γ b I z n
  have hF : Measurable (sourceActualForest t b K) :=
    measurable_killedChildRecords _ _ _ _ _
  have hE : MeasurableSet E :=
    (sourceCoarseTerminalForestEvent_measurable t A γ b I z n).preimage
      ((hF.comp measurable_fst).prodMk measurable_snd)
  have hf := (Measure.quasiMeasurePreserving_fst
    (μ := pathLaw) (ν := independentBridgeLaw ℕ)).ae
      (domainExit_ne_top_ae (diskFinset (Real.exp t)) 0)
  have heq : E =ᵐ[pathLaw.prod (independentBridgeLaw ℕ)]
      sourceLocalTimeBridgeSuccessEvent t A γ b I z := by
    filter_upwards [hf] with p hp
    apply propext
    exact ht A γ b I z ha hcut hblo hbhi p.1 hp p.2
  exact hE.nullMeasurableSet.congr
    (heq.trans (source_walk_bridge_continuous_ae t A γ b I z hγ))

end SRWTightness
