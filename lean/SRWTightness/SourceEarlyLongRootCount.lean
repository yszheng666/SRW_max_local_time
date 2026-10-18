import SRWTightness.BufferedLongRootCount
import SRWTightness.SourceEarlyLongEscape

open Filter
namespace SRWTightness

/-- The original source long segment has a geometric short-root count, with no fine-record error. -/
theorem source_early_long_root_count (hP : PotentialKernelAsymptoticInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → 3 ≤ J → J ≤ ν →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ b x : Site, x ∈ sourceEntranceDomain m 1 ℓ b ν →
      ρ - 14 - 1 ≤ Real.sqrt (normSq (x - b)) → Real.sqrt (normSq (x - b)) ≤ ρ - 14 →
      ∀ k : ℕ,
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      let E := C * 15 / (ρ - 14) * ((k : ℝ) + 1)
      let event := {ω | (killedChildIntervals (sourceExitDomain m 1 ℓ b (ν - J))
        (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν) x ω).length = k + 1}
      Real.exp (-E) * (p * (1 - p) ^ k) ≤ pathLaw.real event ∧
        pathLaw.real event ≤ Real.exp E * (p * (1 - p) ^ k) := by
  obtain ⟨C, T, hC, hT, hh⟩ := buffered_long_root_count hP
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (max 112 (15 * T + 14))),
    eventually_ge_atTop (0 : ℝ)] with t hN ht hm ht0
  intro ν J hν hJ hJν
  dsimp only
  intro b x hx hxlo hxhi k
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
  have hm112 : 112 ≤ m := (le_max_left _ _).trans hm
  have hmT : 15 * T + 14 ≤ m := (le_max_right _ _).trans hm
  have hJreal : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  have hx' : x ∈ translateFinset b (diskFinset (ρ - 14)) := by
    simpa only [sourceEntranceDomain, sourceRecordBuffer, mul_one,
      show (4 : ℝ) + 10 = 14 by norm_num] using hx
  have hb := hh ρ 14 (J : ℝ) (by norm_num) (by linarith) (by nlinarith) hJreal b x hx' hxlo hxhi k
  dsimp only [ρ] at hb
  rw [sourceRecordRadius_successor, sourceRecordRadius_long m ℓ ν J hJν] at hb
  norm_num only at hb
  simpa only [sourceExitDomain, sourceEntranceDomain, sourceLongEscapeParameter,
    sourceRecordBuffer, mul_one, show (4 : ℝ) + 10 = 14 by norm_num] using hb

end SRWTightness
