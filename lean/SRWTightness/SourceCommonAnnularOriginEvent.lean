import SRWTightness.SourceCommonOriginEvent
import SRWTightness.SourceCommonRootGeometry

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- Origin-started single-root common-prefix events obey the reference upper comparison. -/
theorem source_common_annular_origin_event_upper (hinput : PotentialKernelAsymptoticInput)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      1 ≤ Real.sqrt (normSq (w - b)) →
      Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let m := sourceCommonPairInnerRadius t j
      let K := sourceCommonPairObservation b w
      let μ := referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
        (sourceReferenceIntensity m 14)
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) j)]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) j)]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) j))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) j))],
      MarkedGWTreeInput (Mark K) →
      ∀ s : Set (FiniteExcursionRecord (Mark K) j),
      (∀ r ∈ s, ∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      pathLaw {ω | ∃ r ∈ s, killedChildRecords (diskFinset (Real.exp t))
        (growingRecordEntrance b m 14 j) (growingRecordExit b m 14 j) 0
        (actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (wordOccupationMark K) j) ω = [r]} ≤
        ENNReal.ofReal (Real.exp ε) * finiteRecordReferenceMass μ j s := by
  filter_upwards [source_common_origin_event_upper hinput ε hε,
    source_common_root_annular_geometry] with t ht hg
  intro b w j hbw hρ ho hi hd
  dsimp only
  intro hlo hhi inst₁ inst₂ inst₃ inst₄ hmarked s hbar
  have hgeo := hg b j hlo hhi
  exact ht b w j hbw hρ ho hi hd hgeo.2 hgeo.1 hmarked s hbar

end SRWTightness
