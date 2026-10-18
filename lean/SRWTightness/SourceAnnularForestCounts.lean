import SRWTightness.SourceProfileForestCounts
import SRWTightness.SourceForestApplicationGeometry

open MeasureTheory
open scoped ENNReal BigOperators

namespace SRWTightness

/-- The manuscript annular centers at R=exp(t) satisfy the count-controlled forest upper bound. -/
theorem source_annular_forest_count_upper (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧
    ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) → MarkedGWTreeInput (Mark K) →
      ∀ (ℓ k : ℕ), ℓ = sourceRootDepth (Real.exp t) (sourceLowerRadius t) → k < ℓ →
      (Real.exp t) / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ (Real.exp t) / 3 →
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

        pathLaw {ω | killedChildRecords (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b k)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b k) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n) ω ∈ s} ≤
          ENNReal.ofReal ((1 - 1 / ((k : ℝ) + sourceRootReturnShift)) ^ (j - 1) *
            Real.exp E) * independentForestLaw μ j s := by
  obtain ⟨B, W, T₁, hB, hW, hh⟩ := source_profile_forest_count_upper hinput
  obtain ⟨T₂, hlarge⟩ := source_outer_scale_large
  refine ⟨B, W, max T₁ T₂, hB, hW, ?_⟩
  intro b t a K ht ha hcut hK hmarked ℓ k hℓ hk hblo hbhi
  intro inst₁ inst₂ inst₃ inst₄
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ t := (le_max_right _ _).trans ht
  have hs := hlarge t ht₂
  have hm := sourceLowerRadius_pos t
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) hs.1).2.2.1
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by nlinarith [hs.2]
  have hg := source_annular_center_geometry (Real.exp t) (sourceLowerRadius t)
    hm70 hscale b hblo hbhi k
  rw [← hℓ] at hg
  exact hh b t a (Real.exp t) K ht₁ ha hcut hK hmarked hscale le_rfl ℓ k hℓ hk hg.1 hg.2

end SRWTightness
