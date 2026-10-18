import SRWTightness.SourceAnnularSingleRootEvent
import SRWTightness.SourceRootCoarseCounts

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- Concrete source-coarse joint events inherit the actual single-root comparison with vanishing error. -/
theorem source_annular_coarse_event_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W c T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 0 < c ∧
    ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) → MarkedGWTreeInput (Mark K) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ ℓ : ℕ, ℓ = sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))],
      let n := ℓ - 1
      let μ := finiteRecordReferenceMeasure
        (referenceMarkLaw
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
          (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
      ∀ s : Set (List (FiniteExcursionRecord (Mark K) n)),
        (∀ rs ∈ s, rs.length = 1) →
        (∀ r, [r] ∈ s → ∀ j : ℕ, 0 < j → j ≤ n →
          geometricGWHeight (finiteRecordPopulationList n r) j ≤
            4 + sourceBarrierSlope t * j -
              (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) →
      let E := sourceForestQuadraticError B W 8 t
      let p := pathLaw {ω | killedChildRecords (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n) ω ∈ s}
      ENNReal.ofReal (c * Real.exp (-E)) * independentForestLaw μ 1 s ≤ p ∧
        p ≤ ENNReal.ofReal (Real.exp E) * independentForestLaw μ 1 s := by
  obtain ⟨B, W, c, T₁, hB, hW, hc, hh⟩ := source_annular_single_root_event hinput
  obtain ⟨T₂, hbound⟩ := eventually_atTop.mp (source_coarse_root_error_bound B W hB hW)
  refine ⟨B, W, c, max T₁ T₂, hB, hW, hc, ?_⟩
  intro b t a K ht ha hcut hK hmarked hblo hbhi ℓ hℓ
  intro inst₁ inst₂ inst₃ inst₄
  dsimp only
  intro s hlen hcoarse
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ t := (le_max_right _ _).trans ht
  apply hh b t a K ht₁ ha hcut hK hmarked hblo hbhi ℓ hℓ s _ hlen
  intro r hrs
  have hb := hbound t ht₂
  dsimp only at hb
  rw [← hℓ] at hb
  exact hb a ha hcut (Mark K) r (hcoarse r hrs)

end SRWTightness
