import SRWTightness.SourceEarlyOrderedOriginEvent
import SRWTightness.SourceCommonRootGeometry

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- The original source annulus supplies the geometry for early ordered single-root events. -/
theorem source_early_ordered_annular_origin_event_upper (hinput : PotentialKernelAsymptoticInput) :
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
      ∀ s : Set (FiniteExcursionRecord WordMark j),
      (∀ r ∈ s, ∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      pathLaw {ω | ∃ r ∈ s, killedChildRecords (diskFinset (Real.exp t))
        (growingRecordEntrance b m 14 j) (growingRecordExit b m 14 j) 0
        (actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14)
          (firstEntranceWordOfWord (growingRecordExit b m 14 0) K) j) ω = [r]} ≤
        ENNReal.ofReal (Real.exp E) * finiteRecordReferenceMass μ j s := by
  obtain ⟨E, hE, Jmin, hh⟩ := source_early_ordered_origin_event_upper hinput
  refine ⟨E, hE, Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hh⟩ := hh J₀ hJ₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [hh, source_common_root_annular_geometry] with t ht hg
  intro b w hbw ha hrange
  dsimp only
  intro hlo hhi inst₁ inst₂ inst₃ inst₄ hmarked s hbar
  have hgeo := hg b
    (sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) -
      sourceEarlyDistanceGap
        (sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))) J₀) hlo hhi
  exact ht b w hbw ha hrange hgeo.2 hgeo.1 hmarked s hbar

end SRWTightness
