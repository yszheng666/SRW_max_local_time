import SRWTightness.BufferedLongChildExitAtoms
import SRWTightness.SourceEarlyLongEscape

open MeasureTheory Filter
namespace SRWTightness

/-- Actual early source ordered child-record atoms have a uniform prescribed-exit comparison. -/
theorem source_long_child_exit_atoms (hR : TraceExcursionReconstructionInput)
    (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ C J₀ : ℝ, 0 < C ∧ 1 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → J₀ ≤ (J : ℝ) → J ≤ ν →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      ∀ b x e : Site, x ∈ sourceEntranceDomain m 1 ℓ b ν →
      e ∉ sourceExitDomain m 1 ℓ b (ν - J) →
      0 < traceExitProbability (sourceExitDomain m 1 ℓ b (ν - J)) x e →
      ∀ (M : Type*) (F : Site → PathWord → M) (rs : List M),
      let D := sourceExitDomain m 1 ℓ b (ν - J)
      let δ := C * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
      let event := {ω | killedChildRecords D (sourceEntranceDomain m 1 ℓ b ν)
        (sourceExitDomain m 1 ℓ b ν) x F ω = rs}
      let joint := pathLaw.real {ω | ω ∈ event ∧ domainExitLocation D x ω = e}
      Real.exp (-δ) * pathLaw.real event ≤ joint / traceExitProbability D x e ∧
        joint / traceExitProbability D x e ≤ Real.exp δ * pathLaw.real event := by
  obtain ⟨C, J₀, hC, hJ₀, hh⟩ := buffered_long_child_exit_atoms hR hP hH hM hT
  refine ⟨C, J₀, hC, hJ₀, ?_⟩
  filter_upwards [source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (112 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hN ht hm ht0
  intro ν J hν hJ hJν
  dsimp only
  intro b x e hx he hep M F rs
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := sourceRecordRadius m ℓ (ν + 1)
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [ht ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hνℓ : ν + 1 ≤ ℓ := by
    have hpos : 0 < ℓ - 1 := hN.1
    omega
  have hrad : m ≤ ρ := sourceRecordRadius_ge_terminal m (sourceLowerRadius_pos t).le ℓ (ν + 1) hνℓ
  have hρ112 : 112 ≤ ρ := hm.trans hrad
  have hx' : x ∈ translateFinset b (diskFinset (ρ - 14)) := by
    simpa only [sourceEntranceDomain, sourceRecordBuffer, mul_one,
      show (4 : ℝ) + 10 = 14 by norm_num] using hx
  have hlong : translateFinset b (diskFinset (Real.exp ((J : ℝ) + 1) * ρ + 14)) =
      sourceExitDomain m 1 ℓ b (ν - J) := by
    dsimp [ρ]
    rw [sourceRecordRadius_long m ℓ ν J hJν]
    norm_num [sourceExitDomain, sourceRecordBuffer]
  have he' : e ∉ translateFinset b (diskFinset (Real.exp ((J : ℝ) + 1) * ρ + 14)) := by
    simpa only [hlong] using he
  have hep' : 0 < traceExitProbability
      (translateFinset b (diskFinset (Real.exp ((J : ℝ) + 1) * ρ + 14))) x e := by
    simpa only [hlong] using hep
  have hb := hh ρ 14 (J : ℝ) (by norm_num) (by linarith) hJ
    b x e hx' he' hep' M F rs
  dsimp only at hb
  rw [hlong] at hb
  dsimp only [ρ] at hb
  rw [sourceRecordRadius_successor] at hb
  simpa only [sourceExitDomain, sourceEntranceDomain, sourceRecordBuffer, mul_one,
    show (4 : ℝ) + 10 = 14 by norm_num] using hb

end SRWTightness
