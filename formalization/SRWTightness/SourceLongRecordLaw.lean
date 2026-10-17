import SRWTightness.SourceLongFineRecord
import SRWTightness.BufferedLongRecordEstimate
import SRWTightness.SourceRootGWHorizon
import SRWTightness.SourceContinuationRange
import SRWTightness.SourceReferenceIntensityLimit

open Filter
namespace SRWTightness

/-- The actual source fine records in an unconditioned long segment have the geometric product reference law. -/
theorem source_long_record_law (hP : PotentialKernelAsymptoticInput) :
    ∃ C B W : ℝ, 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b : Site) (a : ℝ) (K : Finset Site), 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) → ∀ ν J : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → 3 ≤ J → J ≤ ν →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ x : Site, x ∈ sourceEntranceDomain m 1 ℓ b ν →
      ρ - 14 - 1 ≤ Real.sqrt (normSq (x - b)) → Real.sqrt (normSq (x - b)) ≤ ρ - 14 →
      ∀ (r : FiniteExcursionRecord (Mark K) (ℓ - (ν + 1)))
        (rs : List (FiniteExcursionRecord (Mark K) (ℓ - (ν + 1)))),
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      let E := C * 15 / (ρ - 14) * ((rs.length : ℝ) + 1) +
        ((r :: rs).map (sourceLongFineError B W t a K ν)).sum
      let weight := p * (1 - p) ^ rs.length * ((r :: rs).map (sourceLongFineReferenceMass t b K ν)).prod
      let event := {ω | killedChildRecords (sourceExitDomain m 1 ℓ b (ν - J))
        (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν) x
        (sourceLongFineRecord t b K ν) ω = r :: rs}
      Real.exp (-E) * weight ≤ pathLaw.real event ∧ pathLaw.real event ≤ Real.exp E * weight := by
  obtain ⟨C, T, hC, hT, hh⟩ := buffered_long_record_estimate hP
  obtain ⟨B, W, t₀, hB, hW, hf⟩ := source_long_fine_record_comparison hP
  refine ⟨C, B, W, hC, hB, hW, ?_⟩
  filter_upwards [source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (max 112 (15 * T + 14))),
    eventually_ge_atTop t₀, eventually_ge_atTop (0 : ℝ)] with t hN ht hm ht₀ ht0
  intro b a K ha hcut hK ν J hν hJ hJν
  dsimp only
  intro x hx hxlo hxhi r rs
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
  have hshort : translateFinset b (diskFinset (Real.exp 1 * ρ + 14)) = sourceExitDomain m 1 ℓ b ν := by
    dsimp only [ρ, sourceExitDomain, sourceRecordBuffer]
    rw [sourceRecordRadius_successor]
    norm_num
  have hlong : translateFinset b (diskFinset (Real.exp ((J : ℝ) + 1) * ρ + 14)) =
      sourceExitDomain m 1 ℓ b (ν - J) := by
    dsimp only [ρ, sourceExitDomain, sourceRecordBuffer]
    rw [sourceRecordRadius_long m ℓ ν J hJν]
    norm_num
  have hinner : translateFinset b (diskFinset (ρ - 14)) = sourceEntranceDomain m 1 ℓ b ν := by
    norm_num [sourceEntranceDomain, sourceRecordBuffer, ρ]
  have hp : bufferedLongEscapeParameter ρ 14 (J : ℝ) = sourceLongEscapeParameter m 1 ℓ ν J := by
    norm_num [sourceLongEscapeParameter, sourceRecordBuffer, ρ]
  have hQ : ∀ u, 0 ≤ sourceLongFineReferenceMass t b K ν u := by
    intro u
    exact finiteRecordReferenceWeight_nonneg _ (fun _ ↦ MeasureTheory.measureReal_nonneg) _ u
  have hF : ∀ z : Site, ρ - 14 - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ ρ - 14 → ∀ u,
      Real.exp (-sourceLongFineError B W t a K ν u) * sourceLongFineReferenceMass t b K ν u ≤
        pathLaw.real {ω | sourceLongFineRecord t b K ν z
          (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + 14))) z ω) = u} ∧
      pathLaw.real {ω | sourceLongFineRecord t b K ν z
          (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + 14))) z ω) = u} ≤
        Real.exp (sourceLongFineError B W t a K ν u) * sourceLongFineReferenceMass t b K ν u := by
    intro z hzlo hzhi u
    rw [hshort]
    exact hf b t a K ht₀ ha hcut hK ν (by change ν < ℓ; omega) z u hzlo hzhi
  have hb := hh ρ 14 (J : ℝ) (by norm_num) (by linarith) (by nlinarith) hJreal _ b
    (sourceLongFineRecord t b K ν) (sourceLongFineError B W t a K ν)
    (sourceLongFineReferenceMass t b K ν) hQ hF x (by rw [hinner]; exact hx) hxlo hxhi r rs
  dsimp only at hb
  rw [hlong, hinner, hshort, hp] at hb
  norm_num only at hb
  exact hb

end SRWTightness
