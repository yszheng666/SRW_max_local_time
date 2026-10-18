import SRWTightness.BufferedLongTraceComparison
import SRWTightness.SourceEarlyLongEscape

open MeasureTheory Filter
namespace SRWTightness

/-- Actual early source long exits can be removed uniformly for retained-trace and auxiliary events. -/
theorem source_long_trace_comparison (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ C J₀ : ℝ, 0 < C ∧ 1 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → J₀ ≤ (J : ℝ) → J ≤ ν →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun b ↦ translateFinset b (diskFinset (sourceRecordRadius m ℓ ν + 16))
      ∀ b x e : Site, x ∈ K b → e ∉ sourceExitDomain m 1 ℓ b (ν - J) →
      0 < traceExitProbability (sourceExitDomain m 1 ℓ b (ν - J)) x e →
      ∀ (Ξ : Type*) [MeasurableSpace Ξ] [MeasurableSpace (List Site)]
        (μ : Measure Ξ) [IsProbabilityMeasure μ] (s : Set (List Site × Ξ)), MeasurableSet s →
      let D := sourceExitDomain m 1 ℓ b (ν - J)
      let δ := C * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
      let event := {p : Sample × Ξ | (killedVisitTrace D (K b) x p.1, p.2) ∈ s}
      let joint := ((pathLaw.restrict {ω | domainExitLocation D x ω = e}).prod μ).real event
      Real.exp (-δ) * (pathLaw.prod μ).real event ≤ joint / traceExitProbability D x e ∧
        joint / traceExitProbability D x e ≤ Real.exp δ * (pathLaw.prod μ).real event := by
  obtain ⟨C, J₀, hC, hJ₀, hh⟩ := buffered_long_trace_comparison hP hH hM hT
  refine ⟨C, J₀, hC, hJ₀, ?_⟩
  filter_upwards [source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (14 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hN ht hm ht0
  intro ν J hν hJ hJν
  dsimp only
  intro b x e hx he hep Ξ _ _ μ _ s hs
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := sourceRecordRadius m ℓ (ν + 1)
  let K := translateFinset b (diskFinset (sourceRecordRadius m ℓ ν + 16))
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [ht ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hνℓ : ν + 1 ≤ ℓ := by
    have hpos : 0 < ℓ - 1 := hN.1
    omega
  have hrad : m ≤ ρ := sourceRecordRadius_ge_terminal m (sourceLowerRadius_pos t).le ℓ (ν + 1) hνℓ
  have hρ14 : 14 ≤ ρ := hm.trans hrad
  have hshort : Real.exp 1 * ρ + 14 + 2 = sourceRecordRadius m ℓ ν + 16 := by
    dsimp [ρ]
    rw [sourceRecordRadius_successor]
    ring
  have hlong : translateFinset b (diskFinset (Real.exp ((J : ℝ) + 1) * ρ + 14)) =
      sourceExitDomain m 1 ℓ b (ν - J) := by
    dsimp [ρ]
    rw [sourceRecordRadius_long m ℓ ν J hJν]
    norm_num [sourceExitDomain, sourceRecordBuffer]
  have hK : K ⊆ translateFinset b (diskFinset (Real.exp 1 * ρ + 14 + 2)) := by
    rw [hshort]
  have he' : e ∉ translateFinset b (diskFinset (Real.exp ((J : ℝ) + 1) * ρ + 14)) := by
    simpa only [hlong] using he
  have hep' : 0 < traceExitProbability
      (translateFinset b (diskFinset (Real.exp ((J : ℝ) + 1) * ρ + 14))) x e := by
    simpa only [hlong] using hep
  have hb := hh ρ 14 (J : ℝ) (by linarith) (by norm_num) hρ14 hJ
    b x e K hK hx he' hep' Ξ μ s hs
  dsimp only at hb
  rw [hlong] at hb
  exact hb

end SRWTightness
