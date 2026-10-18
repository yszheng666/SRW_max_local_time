import SRWTightness.SourceEarlyOrderedWeighted
import SRWTightness.SourceEarlyOrderedLeafRoots
import SRWTightness.SourceOrderedPrefixMeasurable

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- Original joint-root weights on the early prefix are dominated by the ordered reference tree. -/
theorem source_early_original_root_weighted (hinput : PotentialKernelAsymptoticInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let j := a - sourceEarlyDistanceGap a J₀
      let ν := a + sourceEarlyDistanceGap a J₀ + 5
      let m := sourceCommonPairInnerRadius t j
      let K := sourceCommonPairObservation b w
      let μ := referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
        (sourceReferenceIntensity m 14)
      (∀ z ∈ ({b, w} : Finset Site), Real.exp t / 4 ≤ Real.sqrt (normSq z) ∧
        Real.sqrt (normSq z) ≤ Real.exp t / 3) →
      ∀ [MeasurableSpace (FiniteExcursionRecord WordMark j)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
        [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))],
      MarkedGWTreeInput WordMark →
      ∀ H : ℕ × ℕ → ℝ≥0∞,
      (∫⁻ ω in sourceEarlyPrefixEvent t b j,
        H (sourceActualCount t b ν ω, sourceActualCount t w ν ω) ∂pathLaw) ≤
        ENNReal.ofReal (Real.exp E) * ∫⁻ r in sourceOrderedPrefixRecords t j,
          H (((finiteRecordLeaves j r).map (sourceCommonWordRootCount t b ν)).sum,
            ((finiteRecordLeaves j r).map (sourceCommonWordRootCount t w ν)).sum)
            ∂finiteRecordReferenceMeasure μ j := by
  obtain ⟨E, hE, JW, hw⟩ := source_early_ordered_prefix_weighted hinput
  obtain ⟨JR, hr⟩ := source_early_ordered_leaf_roots hFlat
  refine ⟨E, hE, max JW JR, ?_⟩
  intro J₀ hJ₀
  obtain ⟨aW, haW, hw⟩ := hw J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨aR, haR, hr⟩ := hr J₀ ((le_max_right _ _).trans hJ₀)
  refine ⟨aW + aR, by omega, ?_⟩
  filter_upwards [hw, hr] with t hw hr
  intro b w hbw ha hrange
  dsimp only
  intro hann inst₁ inst₂ inst₃ inst₄ hmarked H
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let j := a - sourceEarlyDistanceGap a J₀
  let ν := a + sourceEarlyDistanceGap a J₀ + 5
  let f : FiniteExcursionRecord WordMark j → ℝ≥0∞ := fun r ↦
    H (((finiteRecordLeaves j r).map (sourceCommonWordRootCount t b ν)).sum,
      ((finiteRecordLeaves j r).map (sourceCommonWordRootCount t w ν)).sum)
  have hb := hann b (by simp)
  have hbound := hw b w hbw (show aW ≤ _ by omega) hrange hb.1 hb.2 hmarked f
  have heq : (∫⁻ ω in sourceEarlyPrefixEvent t b j,
      H (sourceActualCount t b ν ω, sourceActualCount t w ν ω) ∂pathLaw) =
      ∫⁻ ω in sourceEarlyPrefixEvent t b j,
        ((sourceCommonOrderedForest t b (sourceCommonPairObservation b w) j ω).map f).sum
          ∂pathLaw := by
    apply setLIntegral_congr_fun_ae (measurableSet_sourceEarlyPrefixEvent t b j)
    filter_upwards [domainExit_ne_top_ae (diskFinset (Real.exp t)) 0] with ω hfin
    intro hω
    obtain ⟨r, _, hforest⟩ :=
      (source_ordered_prefix_event_iff t b (sourceCommonPairObservation b w) j ω).mp hω
    have hcounts := hr b w hbw (show aR ≤ _ by omega) hrange hann ω r hfin hforest
    rw [hforest]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    dsimp only [f]
    rw [hcounts b (by simp), hcounts w (by simp)]
  rw [heq]
  exact hbound

end SRWTightness
