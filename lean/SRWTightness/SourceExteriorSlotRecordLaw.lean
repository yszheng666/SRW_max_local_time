import SRWTightness.SourceExteriorReachableExit
import SRWTightness.SourceConditionedLongRecordLaw

open Filter
namespace SRWTightness

/-- The conditional fine-record comparison applies to every slot of the actual exterior record. -/
theorem source_exterior_slot_record_law (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C B W J₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ s ∈ h.1, let z := if s.2.1 then w else b
      ∀ (a : ℝ) (K : Finset Site), 1 ≤ a → a ≤ m / t ^ 6 →
      K ⊆ translateFinset z (diskFinset a) →
      ∀ (r : FiniteExcursionRecord (Mark K) (ℓ - (ν + 1)))
        (rs : List (FiniteExcursionRecord (Mark K) (ℓ - (ν + 1)))),
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      let E := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
        (C * 15 / (ρ - 14) * ((rs.length : ℝ) + 1) +
        ((r :: rs).map (sourceLongFineError B W t a K ν)).sum)
      let weight := p * (1 - p) ^ rs.length * ((r :: rs).map (sourceLongFineReferenceMass t z K ν)).prod
      let event := {ω | killedChildRecords (sourceExitDomain m 1 ℓ z (ν - J))
        (sourceEntranceDomain m 1 ℓ z ν) (sourceExitDomain m 1 ℓ z ν) s.2.2.1
        (sourceLongFineRecord t z K ν) ω = r :: rs}
      let conditional := pathLaw.real {ω | ω ∈ event ∧
        domainExitLocation (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 ω = s.2.2.2} /
        traceExitProbability (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 s.2.2.2
      Real.exp (-E) * weight ≤ conditional ∧ conditional ≤ Real.exp E * weight := by
  obtain ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, hlaw⟩ :=
    source_conditioned_long_record_law hR hP hH hM hT
  refine ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hlaw, source_exterior_entrance_shell, source_exterior_exit_positive hF]
    with t ht hshell hexit
  intro b w ν J hb hw hbw hd hν hform hJ
  dsimp only
  intro h hh s hs
  intro a K ha hcut hK r rs
  obtain ⟨hx, hxlohi, he⟩ := hshell b w ν J hb hw hbw hd hν hform h hh s hs
  have hep := hexit b w ν J hb hw hbw hd hν hform h hh s hs
  exact ht _ a K ha hcut hK ν J hν hJ (by omega) _ _ hx hxlohi.1 hxlohi.2 he hep r rs

end SRWTightness
