import SRWTightness.SourceAnnularCoarseAuxiliary
import SRWTightness.SourceCoarseTerminalForestEvent

open MeasureTheory

namespace SRWTightness

/-- The complete measurable coarse/terminal source event satisfies the actual SRW comparison. -/
theorem source_annular_terminal_auxiliary (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W c T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 0 < c ∧
    ∀ (b : Site) (t A γ : ℝ) (I : ℕ),
      let a := A * diskEnergyGapRatio ^ I
      let K := translateFinset b (diskFinset a)
      ∀ z : K,
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      MarkedGWTreeInput (Mark K) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ ℓ : ℕ, ℓ = sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))],
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))],
      let n := ℓ - 1
      let μ := finiteRecordReferenceMeasure
        (referenceMarkLaw
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
          (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
      let F := killedChildRecords (diskFinset (Real.exp t))
        (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
        (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
        (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
          (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n)
      let S := sourceCoarseTerminalForestEvent t A γ b I z n
      let E := sourceForestQuadraticError B W 8 t
      let ν := independentBridgeLaw ℕ
      let p := (pathLaw.prod ν).real ((fun p ↦ (F p.1, p.2)) ⁻¹' S)
      let q := ((independentForestLaw μ 1).prod ν).real S
      c * Real.exp (-E) * q ≤ p ∧ p ≤ Real.exp E * q := by
  obtain ⟨B, W, c, T, hB, hW, hc, hh⟩ :=
    source_annular_coarse_auxiliary (ℕ → GaussianCoefficientSpace) (independentBridgeLaw ℕ) hinput
  refine ⟨B, W, c, T, hB, hW, hc, ?_⟩
  intro b t A γ I
  dsimp only
  intro z ht ha hcut hmarked hblo hbhi ℓ hℓ instM instMS inst₁ inst₂ inst₃ inst₄
  exact hh b t (A * diskEnergyGapRatio ^ I)
    (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ht ha hcut
    (Finset.Subset.refl _) hmarked hblo hbhi ℓ hℓ
    (sourceCoarseTerminalForestEvent t A γ b I z (ℓ - 1))
    (sourceCoarseTerminalForestEvent_measurable t A γ b I z (ℓ - 1))
    (source_coarse_terminal_forest_length t A γ b I z (ℓ - 1))
    (source_coarse_terminal_forest_barrier t A γ b I z (ℓ - 1))

end SRWTightness
