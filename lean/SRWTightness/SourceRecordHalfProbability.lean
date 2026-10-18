import SRWTightness.SourceRecordRadii

namespace SRWTightness

/-- Source (2.23) uniformly over all record levels and both admissible middle boundary layers. -/
theorem source_record_half_probabilities (hinput : PotentialKernelAsymptoticInput) :
    ∃ K T : ℝ, 0 ≤ K ∧ 2 ≤ T ∧ ∀ m r : ℝ, 0 ≤ r →
      8 * sourceRecordBuffer r ≤ m → T ≤ m - sourceRecordBuffer r →
      ∀ ℓ j : ℕ, j + 2 ≤ ℓ → ∀ b x : Site,
        ((sourceRecordRadius m ℓ (j + 1) - sourceRecordBuffer r - 1 ≤
            Real.sqrt (normSq (x - b)) ∧
          Real.sqrt (normSq (x - b)) ≤ sourceRecordRadius m ℓ (j + 1) - sourceRecordBuffer r) ∨
        (sourceRecordRadius m ℓ (j + 1) + sourceRecordBuffer r ≤
            Real.sqrt (normSq (x - b)) ∧
          Real.sqrt (normSq (x - b)) ≤ sourceRecordRadius m ℓ (j + 1) + sourceRecordBuffer r + 1)) →
        |pathLaw.real {ω |
          domainExit (translateFinset b (diskFinset (sourceRecordRadius m ℓ j + sourceRecordBuffer r))) x ω <
          setHittingTime (translateFinset b
            (diskFinset (sourceRecordRadius m ℓ (j + 2) - sourceRecordBuffer r))) x 0 ω} - 1 / 2| ≤
          K * sourceRecordBuffer r / sourceRecordRadius m ℓ (j + 2) ∧
        |setHitProbability
          (translateFinset b (diskFinset (sourceRecordRadius m ℓ j + sourceRecordBuffer r)))
          (translateFinset b (diskFinset (sourceRecordRadius m ℓ (j + 2) - sourceRecordBuffer r))) x - 1 / 2| ≤
          K * sourceRecordBuffer r / sourceRecordRadius m ℓ (j + 2) := by
  obtain ⟨K, T, hK, hT, hh⟩ := source_buffered_half_probabilities hinput
  refine ⟨K, T, hK, hT, ?_⟩
  intro m r hr hm hTm ℓ j hj b x hx
  have hH : 1 ≤ sourceRecordBuffer r := by unfold sourceRecordBuffer; linarith
  have hm0 : 0 ≤ m := by linarith
  have hρ := sourceRecordRadius_ge_terminal m hm0 ℓ (j + 2) hj
  have he1 : Real.exp 1 * sourceRecordRadius m ℓ (j + 2) =
      sourceRecordRadius m ℓ (j + 1) := by
    simpa only [Nat.add_assoc] using sourceRecordRadius_successor m ℓ (j + 1)
  have he2 := sourceRecordRadius_two_steps m ℓ j
  have hp := hh (sourceRecordRadius m ℓ (j + 2)) (sourceRecordBuffer r) hH
    (by linarith) (by linarith) b x
  rw [he1, he2] at hp
  exact hp hx

end SRWTightness
