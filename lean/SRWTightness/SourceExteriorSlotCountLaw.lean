import SRWTightness.SourceExteriorReachableExit
import SRWTightness.SourceConditionedLongRootCount

open Filter
namespace SRWTightness

/-- The count-only conditional comparison applies to every actual exterior slot. -/
theorem source_exterior_slot_count_law (hF : ExteriorBridgeFactorizationInput)
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
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ s ∈ h.1, let z := if s.2.1 then w else b
      ∀ k : ℕ,
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      let E := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) + C * 15 / (ρ - 14) * ((k : ℝ) + 1)
      let event := {ω | (killedChildIntervals (sourceExitDomain m 1 ℓ z (ν - J))
        (sourceEntranceDomain m 1 ℓ z ν) (sourceExitDomain m 1 ℓ z ν) s.2.2.1 ω).length = k + 1}
      let conditional := pathLaw.real {ω | ω ∈ event ∧
        domainExitLocation (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 ω = s.2.2.2} /
        traceExitProbability (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 s.2.2.2
      Real.exp (-E) * (p * (1 - p) ^ k) ≤ conditional ∧
        conditional ≤ Real.exp E * (p * (1 - p) ^ k) := by
  obtain ⟨A, C, J₀, hA, hC, hJ₀, hlaw⟩ :=
    source_conditioned_long_root_count hR hP hH hM hT
  refine ⟨A, C, J₀, hA, hC, hJ₀, ?_⟩
  filter_upwards [hlaw, source_exterior_entrance_shell, source_exterior_exit_positive hF]
    with t ht hshell hexit
  intro b w ν J hb hw hbw hd hν hform hJ
  dsimp only
  intro h hh s hs
  intro k
  obtain ⟨hx, hxlohi, he⟩ := hshell b w ν J hb hw hbw hd hν hform h hh s hs
  have hep := hexit b w ν J hb hw hbw hd hν hform h hh s hs
  exact ht ν J hν hJ (by omega) _ _ _ hx hxlohi.1 hxlohi.2 he hep k

end SRWTightness
