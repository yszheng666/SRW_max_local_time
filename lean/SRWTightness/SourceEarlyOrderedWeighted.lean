import SRWTightness.SourceEarlyOrderedAnnularOrigin
import SRWTightness.SourceOrderedPrefixEvent
import SRWTightness.SingletonRecordWeightedComparison

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- The original early prefix controls every nonnegative weight of its selected ordered record. -/
theorem source_early_ordered_prefix_weighted (hinput : PotentialKernelAsymptoticInput) :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let j := a - sourceEarlyDistanceGap a J₀
      let m := sourceCommonPairInnerRadius t j
      let K := sourceCommonPairObservation b w
      let μ := referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
        (sourceReferenceIntensity m 14)
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ [MeasurableSpace (FiniteExcursionRecord WordMark j)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
        [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))],
      MarkedGWTreeInput WordMark →
      ∀ f : FiniteExcursionRecord WordMark j → ℝ≥0∞,
      (∫⁻ ω in sourceEarlyPrefixEvent t b j,
        ((sourceCommonOrderedForest t b K j ω).map f).sum ∂pathLaw) ≤
        ENNReal.ofReal (Real.exp E) *
          ∫⁻ r in sourceOrderedPrefixRecords t j, f r ∂finiteRecordReferenceMeasure μ j := by
  obtain ⟨E, hE, Jmin, hh⟩ := source_early_ordered_annular_origin_event_upper hinput
  refine ⟨E, hE, Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hh⟩ := hh J₀ hJ₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [hh] with t ht
  intro b w hbw ha hrange
  dsimp only
  intro hlo hhi inst₁ inst₂ inst₃ inst₄ hmarked f
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let j := a - sourceEarlyDistanceGap a J₀
  let m := sourceCommonPairInnerRadius t j
  let K := sourceCommonPairObservation b w
  let μ := referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
    (sourceReferenceIntensity m 14)
  let F := sourceCommonOrderedForest t b K j
  let S := sourceOrderedPrefixRecords t j
  letI := finiteExcursionRecord_countable WordMark j
  have hF : Measurable F := measurable_killedChildRecords _ _ _ _ _
  have hc : ∀ s : Set (FiniteExcursionRecord WordMark j), s ⊆ S →
      pathLaw {ω | ∃ r ∈ s, F ω = [r]} ≤
        ENNReal.ofReal (Real.exp E) * finiteRecordReferenceMeasure μ j s := by
    intro s hs
    rw [finiteRecordReferenceMeasure_apply]
    exact ht b w hbw ha hrange hlo hhi hmarked s (fun r hr ↦ hs hr)
  have hpre : F ⁻¹' ((fun r : FiniteExcursionRecord WordMark j ↦ [r]) '' S) =
      sourceEarlyPrefixEvent t b j := by
    ext ω
    constructor
    · rintro ⟨r, hbar, hr⟩
      exact (source_ordered_prefix_event_iff t b K j ω).mpr ⟨r, hbar, hr.symm⟩
    · intro hω
      obtain ⟨r, hbar, hr⟩ := (source_ordered_prefix_event_iff t b K j ω).mp hω
      exact ⟨r, hbar, hr.symm⟩
  have hbound := singleton_record_lintegral_comparison pathLaw
    (finiteRecordReferenceMeasure μ j) F hF S (ENNReal.ofReal (Real.exp E)) hc f
  rw [hpre] at hbound
  exact hbound

end SRWTightness
