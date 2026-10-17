import SRWTightness.SourceProfileForestInternal
import SRWTightness.ForestPopulationError

open MeasureTheory
open scoped ENNReal BigOperators

namespace SRWTightness

/-- Generation count bounds directly control the actual source forest event probability. -/
theorem source_profile_forest_count_upper_internal (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧
    ∀ (b : Site) (t a R : ℝ) (K : Finset Site),
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) →
      32 * sourceLowerRadius t ≤ R → R ≤ Real.exp t →
      ∀ (ℓ k : ℕ), ℓ = sourceRootDepth R (sourceLowerRadius t) → k < ℓ →
      sourceRecordRadius (sourceLowerRadius t) ℓ (k + 1) - 14 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) + (sourceRecordRadius (sourceLowerRadius t) ℓ k + 14) + 1 < R →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) (ℓ - (k + 1)))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) (ℓ - (k + 1)))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) (ℓ - (k + 1))))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) (ℓ - (k + 1))))],
      let n := ℓ - (k + 1)
      let μ := finiteRecordReferenceMeasure
        (referenceMarkLaw
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
          (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
      ∀ (L : ℕ → ℝ) (j : ℕ), 1 ≤ j →
        ∀ (s : Set (List (FiniteExcursionRecord (Mark K) n))),
        (∀ rs ∈ s, rs.length = j) →
        (∀ rs ∈ s, ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ L i) →
        let E := (∑ i ∈ Finset.range n, (L (i + 1) + L i) *
          (4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) i))) +
          (2 * (W * (a + 1) / sourceLowerRadius t *
            Real.log (sourceLowerRadius t / a))) * L 0

        pathLaw {ω | killedChildRecords (diskFinset R)
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b k)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b k) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n) ω ∈ s} ≤
          ENNReal.ofReal ((1 - 1 / ((k : ℝ) + sourceRootReturnShift)) ^ (j - 1) *
            Real.exp E) * independentForestLaw μ j s := by
  obtain ⟨B, W, T, hB, hW, hh⟩ := source_profile_forest_upper_internal hinput
  refine ⟨B, W, max T (sourceScaleThreshold 4), hB, hW, ?_⟩
  intro b t a R K ht ha hcut hK hscale htime ℓ k hℓ hk hout hfit
  intro inst₁ inst₂ inst₃ inst₄
  dsimp only
  intro L j hj s hlen hcounts
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_right _ _).trans ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) htbase).1
  have hm := sourceLowerRadius_pos t
  have ham : a ≤ sourceLowerRadius t :=
    hcut.trans (div_le_self hm.le (one_le_pow₀ (by linarith : 1 ≤ t)))
  have hlog : 0 ≤ Real.log (sourceLowerRadius t / a) :=
    Real.log_nonneg ((le_div_iff₀ (by linarith : 0 < a)).mpr (by simpa using ham))
  apply hh b t a R K htT ha hcut hK hscale htime ℓ k hℓ hk hout hfit
    j hj s _ hlen
  intro rs hrs
  apply forest_error_population_bound
  · intro i hi
    dsimp [growingRecordRadius]
    positivity
  · positivity
  · exact hcounts rs hrs

end SRWTightness
