import SRWTightness.SourceCommonAnnularOriginEvent
import SRWTightness.SourceCommonReferenceHighEvent

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- The origin-started common record event has the full quadratic exponential upper bound. -/
theorem source_common_origin_high_upper (hpot : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      sourceCoarseLowerLevel t ≤ j → 1 ≤ Real.sqrt (normSq (w - b)) →
      Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      let m := sourceCommonPairInnerRadius t j
      let K := sourceCommonPairObservation b w
      ∀ [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))]
        [MeasurableSpace (FiniteExcursionRecord (Mark K) j)]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) j)]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) j))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) j))],
      MarkedGWJointInput (Mark K) →
      ∀ hpair : ({b, w} : Finset Site) ⊆ K,
      pathLaw {ω | ∃ r ∈ sourceCommonPrefixHighEvent t b w j hpair,
        killedChildRecords (diskFinset (Real.exp t)) (growingRecordEntrance b m 14 j)
          (growingRecordExit b m 14 j) 0
          (actualFiniteWordRecord (growingRecordEntrance b m 14)
            (growingRecordExit b m 14) (wordOccupationMark K) j) ω = [r]} ≤
      ENNReal.ofReal (C * t ^ 2 * Real.exp
        (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
            sourceCommonPairRowScale t b w j)) := by
  obtain ⟨C, hC, hreference⟩ := source_common_reference_high_upper hGW hOcc hRes
  refine ⟨Real.exp 1 * C, mul_pos (Real.exp_pos _) hC, ?_⟩
  filter_upwards [hreference, source_common_annular_origin_event_upper hpot 1 (by norm_num)]
    with t hr ho
  intro b w j hbw hcut hρ houter hi hd hlo hhi
  dsimp only
  intro inst₁ inst₂ inst₃ inst₄ inst₅ inst₆ hinput hpair
  have href := hr b w j hbw hcut hi hd hinput hpair
  have hactual := ho b w j hbw hρ houter hi hd hlo hhi
    (markedGWJoint_population hinput) (sourceCommonPrefixHighEvent t b w j hpair)
    (fun r hmem k hk hkj ↦ hmem.1 k hk hkj)
  have hμ : referenceMarkLaw
      (translateFinset b (diskFinset (Real.exp 1 * sourceCommonPairInnerRadius t j + 14)))
      (sourceCommonPairObservation b w) (sourceReferenceIntensity (sourceCommonPairInnerRadius t j) 14) =
      referenceMarkLaw (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w)
        (sourceCommonPairIntensity t j) := by
    rw [sourceCommonPairDomain_eq]
    rfl
  rw [hμ] at hactual
  have hh := hactual.trans (mul_le_mul_left' href (ENNReal.ofReal (Real.exp 1)))
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg 1)] at hh
  convert hh using 1 <;> congr 1 <;> ring

end SRWTightness
