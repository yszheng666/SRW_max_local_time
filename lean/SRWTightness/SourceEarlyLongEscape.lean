import SRWTightness.SourceLongEscapeProbability
import SRWTightness.SourceRootGWHorizon
import SRWTightness.SourceContinuationRange
import SRWTightness.SourceReferenceIntensityLimit

open Filter
namespace SRWTightness

/-- The actual early source scales automatically meet every hypothesis of the long-escape estimate. -/
theorem source_early_long_escape (hP : PotentialKernelAsymptoticInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → 1 ≤ J → J ≤ ν →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      (1 / 2 : ℝ) / ((J : ℝ) + 1) ≤ sourceLongEscapeParameter m 1 ℓ ν J ∧
      sourceLongEscapeParameter m 1 ℓ ν J ≤ 2 / ((J : ℝ) + 1) ∧
      ∀ b x : Site, x ∈ domainExitBoundary (sourceExitDomain m 1 ℓ b ν) →
      ∃ δ : ℝ, |δ| ≤ C * (sourceRecordBuffer 1 + 1) /
          (sourceRecordRadius m ℓ (ν + 1) - sourceRecordBuffer 1) ∧
        pathLaw.real {ω | domainExit (sourceExitDomain m 1 ℓ b (ν - J)) x ω <
          setHittingTime (sourceEntranceDomain m 1 ℓ b ν) x 0 ω} =
          sourceLongEscapeParameter m 1 ℓ ν J * (1 + δ) := by
  obtain ⟨C, T, hC, hT, hh⟩ := source_long_escape_probability hP
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (max 70 (T + 14))),
    eventually_ge_atTop (0 : ℝ)] with t hN ht hm ht0
  intro ν J hν hJ hJν
  let ℓ := sourceRootDepth (Real.exp t) (sourceLowerRadius t)
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [ht ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hνℓ : ν + 1 ≤ ℓ := by
    have hhpos : 0 < ℓ - 1 := hN.1
    omega
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t)
    (sourceLowerRadius_pos t).le ℓ (ν + 1) hνℓ
  have hm70 : 70 ≤ sourceLowerRadius t := (le_max_left _ _).trans hm
  have hmT : T + 14 ≤ sourceLowerRadius t := (le_max_right _ _).trans hm
  apply hh (sourceLowerRadius t) 1 ℓ ν J (by norm_num) _ _ hJ hJν
  · norm_num [sourceRecordBuffer]
    linarith
  · norm_num [sourceRecordBuffer]
    linarith

end SRWTightness
