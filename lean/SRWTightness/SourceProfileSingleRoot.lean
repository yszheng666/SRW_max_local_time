import SRWTightness.SourceProfileRecordComparison
import SRWTightness.SourceSingleRootGeometry

namespace SRWTightness

/-- The actual manuscript root record satisfies the full source-profile comparison. -/
theorem source_profile_single_root_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W t₀ : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      t₀ ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) →
      let η : Mark K → ℝ := fun _ ↦ 2 * (W * (a + 1) / (sourceLowerRadius t) * Real.log ((sourceLowerRadius t) / a))
      let Q : Mark K → ℝ := fun v ↦
        (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * (sourceLowerRadius t) + 14))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * (sourceLowerRadius t) + 14) / ((sourceLowerRadius t) - 14)))).real {v}
      ∀ ℓ k, k < ℓ →
      let n := ℓ - (k + 1)
      ∀ x (r : FiniteExcursionRecord (Mark K) n),
      sourceRecordRadius (sourceLowerRadius t) ℓ (k + 1) - 14 - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ sourceRecordRadius (sourceLowerRadius t) ℓ (k + 1) - 14 →
      Real.exp (-finiteRecordError (fun j ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) j)) η n r) *
          finiteRecordReferenceWeight Q n r ≤
        pathLaw.real {ω | actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
          (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n x
          (killedPathWord (sourceExitDomain (sourceLowerRadius t) 1 ℓ b k) x ω) = r} ∧
      pathLaw.real {ω | actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
          (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n x
          (killedPathWord (sourceExitDomain (sourceLowerRadius t) 1 ℓ b k) x ω) = r} ≤
        Real.exp (finiteRecordError (fun j ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) j)) η n r) *
          finiteRecordReferenceWeight Q n r := by
  obtain ⟨B, W, t₀, hB, hW, hh⟩ := source_profile_record_comparison hinput
  refine ⟨B, W, t₀, hB, hW, ?_⟩
  intro b t a K ht ha hcut hK
  dsimp only
  intro ℓ k hk x r hxlo hxhi
  have hbuffer : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  simp_rw [source_single_root_record _ _ _ _ hk, hbuffer]
  apply hh b t a K ht ha hcut hK (ℓ - (k + 1)) x r
  · simpa only [source_single_root_radius _ ℓ k hk] using hxlo
  · simpa only [source_single_root_radius _ ℓ k hk] using hxhi

end SRWTightness
