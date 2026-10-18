import SRWTightness.SourceReferenceCountLower

open MeasureTheory Filter
namespace SRWTightness

/-- Adjoining the independent source bridges preserves every path-only event. -/
theorem source_enlarged_path_event (S : Set Sample) :
    sourceEnlargedLaw.real {v | v.1 ∈ S} = pathLaw.real S := by
  have he : {v : Sample × (Site → ℕ → GaussianCoefficientSpace) | v.1 ∈ S} =
      S ×ˢ Set.univ := by ext v; simp
  rw [he, sourceEnlargedLaw, measureReal_prod_prod, probReal_univ, mul_one]

/-- The lower mixture comparison on the common source space, in the form required by the
original joint-root aggregation theorem. -/
theorem source_enlarged_reference_count_lower (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C J₀ : ℝ, 0 < A ∧ 0 < C ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      ∀ h : ExteriorPathRecord,
      0 < sourceEnlargedLaw.real {v | sourcePairExteriorRecord t b w ν J v.1 = h} →
      ∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      sourceReferenceJointCountWeight t ν J h k l ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) + C * 15 /
            (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14))) *
        (sourceEnlargedLaw.real {v | sourcePairExteriorRecord t b w ν J v.1 = h ∧
          sourceActualCount t b ν v.1 = k ∧ sourceActualCount t w ν v.1 = l} /
          sourceEnlargedLaw.real {v | sourcePairExteriorRecord t b w ν J v.1 = h}) := by
  obtain ⟨A, C, J₀, hA, hC, hJ₀, ht⟩ :=
    source_reference_count_lower hExt hFlat hR hP hH hM hT
  refine ⟨A, C, J₀, hA, hC, hJ₀, ?_⟩
  filter_upwards [ht] with t hlow
  intro b w ν J hb hw hbw hd hν hform hJ h hh k l hk hl
  have hden := source_enlarged_path_event {ω | sourcePairExteriorRecord t b w ν J ω = h}
  have hnum := source_enlarged_path_event {ω | sourcePairExteriorRecord t b w ν J ω = h ∧
    sourceActualCount t b ν ω = k ∧ sourceActualCount t w ν ω = l}
  simp only [Set.mem_setOf_eq] at hden hnum
  rw [hden] at hh
  rw [hnum, hden]
  exact hlow b w ν J hb hw hbw hd hν hform hJ h hh k l hk hl

end SRWTightness
