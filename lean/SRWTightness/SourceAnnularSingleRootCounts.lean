import SRWTightness.SourceAnnularSingleRootEvent
import SRWTightness.ForestPopulationError

open MeasureTheory
open scoped ENNReal BigOperators

namespace SRWTightness

/-- Count bounds give a two-sided actual single-root event comparison at the manuscript centers. -/
theorem source_annular_single_root_count_event (hinput : PotentialKernelAsymptoticInput) :
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
      ∀ (L : ℕ → ℝ) (s : Set (List (FiniteExcursionRecord (Mark K) n))),
        (∀ rs ∈ s, rs.length = 1) →
        (∀ rs ∈ s, ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ L i) →
      let E := (∑ i ∈ Finset.range n, (L (i + 1) + L i) *
        (4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) i))) +
        (2 * (W * (a + 1) / sourceLowerRadius t *
          Real.log (sourceLowerRadius t / a))) * L 0
      let p := pathLaw {ω | killedChildRecords (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n) ω ∈ s}
      ENNReal.ofReal (c * Real.exp (-E)) * independentForestLaw μ 1 s ≤ p ∧
        p ≤ ENNReal.ofReal (Real.exp E) * independentForestLaw μ 1 s := by
  obtain ⟨B, W, c, T, hB, hW, hc, hh⟩ := source_annular_single_root_event hinput
  refine ⟨B, W, c, max T (sourceScaleThreshold 4), hB, hW, hc, ?_⟩
  intro b t a K ht ha hcut hK hmarked hblo hbhi ℓ hℓ
  intro inst₁ inst₂ inst₃ inst₄
  dsimp only
  intro L s hlen hcounts
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_right _ _).trans ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) htbase).1
  have hm := sourceLowerRadius_pos t
  have ham : a ≤ sourceLowerRadius t :=
    hcut.trans (div_le_self hm.le (one_le_pow₀ (by linarith : 1 ≤ t)))
  have hlog : 0 ≤ Real.log (sourceLowerRadius t / a) :=
    Real.log_nonneg ((le_div_iff₀ (by linarith : 0 < a)).mpr (by simpa using ham))
  apply hh b t a K htT ha hcut hK hmarked hblo hbhi ℓ hℓ s _ hlen
  intro r hrs
  have hb := forest_error_population_bound
    (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) i))
    (2 * (W * (a + 1) / sourceLowerRadius t * Real.log (sourceLowerRadius t / a)))
    (ℓ - 1) [r] L
    (by intro i hi; dsimp [growingRecordRadius]; positivity)
    (by positivity) (hcounts [r] hrs)
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using hb

end SRWTightness
