import SRWTightness.CommonMarkedReferenceEndpointSum
import SRWTightness.SourceCommonPairCoarseReferenceSum
import SRWTightness.SourceCommonPairEndpointPositive
import SRWTightness.SourceTerminalCapacityHalf

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- The complete coarse barrier through the common endpoint. -/
def sourceCommonPrefixGWBarrier (t : ℝ) (j : ℕ) : Set GeometricGWRecord :=
  {g | ∀ k : ℕ, 0 < k → k ≤ j → geometricGWHeight g k ≤ sourceCommonPairEndpoint t k}

/-- The common reference record retains its barrier and both high site occupations. -/
def sourceCommonPrefixHighEvent (t : ℝ) (b w : Site) (j : ℕ)
    (hpair : ({b, w} : Finset Site) ⊆ sourceCommonPairObservation b w) :
    Set (FiniteExcursionRecord (Mark (sourceCommonPairObservation b w)) j) :=
  {r | finiteRecordPopulationList j r ∈ sourceCommonPrefixGWBarrier t j ∧
    finiteRecordLeaves j r ∈ commonPairListHighEvent (sourceCommonPairObservation b w)
      ({b, w} : Finset Site) hpair (geometricGWPopulation (finiteRecordPopulationList j r) j)
        ((2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2)}

/-- The actual joint common reference event has the manuscript quadratic exponential upper bound. -/
theorem source_common_reference_high_upper
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      sourceCoarseLowerLevel t ≤ j →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ [MeasurableSpace (List (Mark (sourceCommonPairObservation b w)))]
        [MeasurableSingletonClass (List (Mark (sourceCommonPairObservation b w)))],
      MarkedGWJointInput (Mark (sourceCommonPairObservation b w)) →
      ∀ hpair : ({b, w} : Finset Site) ⊆ sourceCommonPairObservation b w,
      finiteRecordReferenceMass (referenceMarkLaw (sourceCommonPairDomain t b j)
        (sourceCommonPairObservation b w) (sourceCommonPairIntensity t j)) j
        (sourceCommonPrefixHighEvent t b w j hpair) ≤
      ENNReal.ofReal (C * t ^ 2 * Real.exp
        (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
            sourceCommonPairRowScale t b w j)) := by
  obtain ⟨C, hC, hsum⟩ := source_common_pair_coarse_reference_sum hGW hOcc hRes
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsum, source_common_pair_observation_uniform,
    sourceCoarseLowerLevel_eventually_twenty, source_common_pair_level_range,
    sourceBarrierSlope_eventually_ge_one, eventually_ge_atTop (sourceScaleThreshold 4)]
    with t ht hg hcut hl htheta htbase
  intro b w j hbw hj hi hd inst₁ inst₂ hinput hpair
  have hj1 : 1 ≤ j := by have hh := hcut.trans hj; omega
  have htime := hl j hd
  have hq := sourceCommonPairEndpoint_ge_four t j htheta hj1 (by linarith)
  have hgeom := hg b w j hbw hi
  have hm := ((sourceScaleThreshold_conditions t 4 (by norm_num) htbase).2.2.1).trans
    (sourceCommonPairInnerRadius_ge_lower t j hd)
  have hα := (sourceCommonPairIntensity_bounds t j hm).1.le
  have hc := source_terminal_capacity_half b (sourceCommonPairInnerRadius t j) 14
    (2 * Real.sqrt (normSq (w - b))) (sourceCommonPairObservation b w)
    hgeom.1 hgeom.2.1 (by norm_num) (by linarith) (Finset.Subset.refl _) hgeom.2.2
  have hcap : sourceCommonPairIntensity t j *
      capacity (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w) ≤ 1 := by
    rw [sourceCommonPairDomain_eq]
    exact hc.trans (by norm_num)
  have hh := common_marked_reference_endpoint_sum (sourceCommonPairDomain t b j)
    (sourceCommonPairObservation b w) ({b, w} : Finset Site) hpair
    (sourceCommonPairIntensity t j) ((2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2)
    (sourceCommonPairEndpoint t j) j hα hcap (by linarith) hinput
    (sourceCommonPrefixGWBarrier t j) (fun g hg ↦ hg j hj1 le_rfl)
  exact hh.trans (ENNReal.ofReal_le_ofReal (ht b w j hbw hj hi hd hpair))

end SRWTightness
