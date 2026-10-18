import SRWTightness.SourceAnnularTerminalAuxiliary
import SRWTightness.SourceCoarseTerminalReference

open MeasureTheory

namespace SRWTightness

/-- The actual source success record and bridge probability compares directly to the GW terminal integral. -/
theorem source_annular_terminal_integral (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W c T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 0 < c ∧
    ∀ (b : Site) (t A γ : ℝ) (I : ℕ),
      let a := A * diskEnergyGapRatio ^ I
      let K := translateFinset b (diskFinset a)
      ∀ z : K,
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ ℓ : ℕ, ℓ = sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))],
      MarkedGWJointInput (Mark K) → 0 ≤ γ →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))],
      let n := ℓ - 1
      let F := killedChildRecords (diskFinset (Real.exp t))
        (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
        (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
        (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
          (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n)
      let S := sourceCoarseTerminalForestEvent t A γ b I z n
      let E := sourceForestQuadraticError B W 8 t
      let ν := independentBridgeLaw ℕ
      let p := (pathLaw.prod ν).real ((fun p ↦ (F p.1, p.2)) ⁻¹' S)
      let q := ∫ g in sourceGWCoarseBandEvent t n,
        sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation g n)
          ∂geometricGWRecordLaw 1 n
      c * Real.exp (-E) * q ≤ p ∧ p ≤ Real.exp E * q := by
  obtain ⟨B, W, c, T, hB, hW, hc, hh⟩ := source_annular_terminal_auxiliary hinput
  refine ⟨B, W, c, max T sourceCapacityHalfThreshold, hB, hW, hc, ?_⟩
  intro b t A γ I
  dsimp only
  intro z ht ha hcut hblo hbhi ℓ hℓ instM instMS hjoint hγ inst₁ inst₂ inst₃ inst₄
  have htcap : sourceCapacityHalfThreshold ≤ t := (le_max_right _ _).trans ht
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num)
    ((le_max_left _ _).trans htcap)).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1.le
  have hcap := source_capacity_half_profile b t (A * diskEnergyGapRatio ^ I)
    (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) htcap ha hcut
    (Finset.Subset.refl _)
  have hb := hh b t A γ I z ((le_max_left _ _).trans ht) ha hcut
    (markedGWJoint_population hjoint) hblo hbhi ℓ hℓ
  dsimp only at hb
  rw [source_coarse_terminal_reference_integral t A γ b I z (ℓ - 1)
    hjoint hα (by linarith) hγ] at hb
  exact hb

end SRWTightness
