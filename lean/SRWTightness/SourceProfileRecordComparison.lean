import SRWTightness.GrowingRecordComparison
import SRWTightness.SourceTerminalErrorSmall
import SRWTightness.SourceReferenceIntensityLimit

namespace SRWTightness

/-- The actual source profile satisfies the full geometric record comparison for all large times. -/
theorem source_profile_record_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W t₀ : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      t₀ ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) →
      let η : Mark K → ℝ := fun _ ↦ 2 * (W * (a + 1) / (sourceLowerRadius t) * Real.log ((sourceLowerRadius t) / a))
      let Q : Mark K → ℝ := fun v ↦
        (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * (sourceLowerRadius t) + 14))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * (sourceLowerRadius t) + 14) / ((sourceLowerRadius t) - 14)))).real {v}
      ∀ n x (r : FiniteExcursionRecord (Mark K) n),
      growingRecordRadius (sourceLowerRadius t) n - 14 - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius (sourceLowerRadius t) n - 14 →
      Real.exp (-finiteRecordError (fun j ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) j)) η n r) *
          finiteRecordReferenceWeight Q n r ≤
        pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b (sourceLowerRadius t) 14)
          (growingRecordExit b (sourceLowerRadius t) 14) (wordOccupationMark K) n x
          (killedPathWord (growingRecordExit b (sourceLowerRadius t) 14 n) x ω) = r} ∧
      pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b (sourceLowerRadius t) 14)
          (growingRecordExit b (sourceLowerRadius t) 14) (wordOccupationMark K) n x
          (killedPathWord (growingRecordExit b (sourceLowerRadius t) 14 n) x ω) = r} ≤
        Real.exp (finiteRecordError (fun j ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) j)) η n r) *
          finiteRecordReferenceWeight Q n r := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ := growing_record_probability_comparison hinput
  let t₀ := max sourceCapacityHalfThreshold
    (max (8 * W) (max (56 * B) (max (T + 14) (max M 112))))
  refine ⟨B, W, t₀, hB, hW, ?_⟩
  intro b t a K ht ha hcut hK
  have htcap : sourceCapacityHalfThreshold ≤ t := (le_max_left _ _).trans ht
  have ht1 := (le_max_right _ _).trans ht
  have htW : 8 * W ≤ t := (le_max_left _ _).trans ht1
  have ht2 := (le_max_right _ _).trans ht1
  have htB : 56 * B ≤ t := (le_max_left _ _).trans ht2
  have ht3 := (le_max_right _ _).trans ht2
  have htT : T + 14 ≤ t := (le_max_left _ _).trans ht3
  have ht4 := (le_max_right _ _).trans ht3
  have htM : M ≤ t := (le_max_left _ _).trans ht4
  have ht112 : (112 : ℝ) ≤ t := (le_max_right _ _).trans ht4
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_left _ _).trans htcap
  have hmt := sourceLowerRadius_ge_self t htbase
  have hm0 := sourceLowerRadius_pos t
  have hsmall := source_terminal_smallness_profile b t a W K hW
    (max_le htcap htW) ha hcut hK
  have hsep : 2 * a < sourceLowerRadius t - 14 - 2 := by
    have hp : (2 : ℝ) ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
    norm_num at hp
    have hc := (le_div_iff₀ (by positivity : 0 < t ^ 6)).mp hcut
    nlinarith
  apply hh b (sourceLowerRadius t) 14 a K (by norm_num) (by linarith)
    (by linarith) (htM.trans hmt)
  · apply (div_le_iff₀ hm0).mpr
    nlinarith
  · linarith
  · exact hsep
  · exact hK
  · exact hsmall.1
  · exact hsmall.2

end SRWTightness
