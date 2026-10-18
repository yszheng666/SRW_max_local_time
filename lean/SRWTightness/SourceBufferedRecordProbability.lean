import SRWTightness.BufferedRecordProbability
import SRWTightness.SourceBufferedHalf

namespace SRWTightness

/-- The potential-kernel input gives uniform actual buffered record probability comparisons. -/
theorem source_buffered_record_probability_comparison {M : Type*}
    (hinput : PotentialKernelAsymptoticInput) :
    ∃ K T : ℝ, 0 ≤ K ∧ 2 ≤ T ∧ ∀ (b : Site) (ρ H : ℝ),
    1 ≤ H → 8 * H ≤ ρ → T ≤ ρ - H → K * H / ρ ≤ 1 / 4 →
    ∀ (F : Site → PathWord → M)
    (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hF : ∀ z : Site, ρ - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ ρ - H → ∀ r,
      Real.exp (-η r) * Q r ≤ pathLaw.real {ω |
        F z (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = r} ∧
      pathLaw.real {ω |
        F z (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) z ω) = r} ≤
        Real.exp (η r) * Q r),
    ∀ rs x, x ∈ bufferedRecordMiddle b ρ H →
      Real.exp (-orderedRecordError (4 * (K * H / ρ)) η rs) * orderedReferenceWeight Q rs ≤
        pathLaw.real {ω | killedChildRecords
          (translateFinset b (diskFinset (Real.exp 2 * ρ + H)))
          (translateFinset b (diskFinset (ρ - H)))
          (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) x F ω = rs} ∧
      pathLaw.real {ω | killedChildRecords
          (translateFinset b (diskFinset (Real.exp 2 * ρ + H)))
          (translateFinset b (diskFinset (ρ - H)))
          (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) x F ω = rs} ≤
        Real.exp (orderedRecordError (4 * (K * H / ρ)) η rs) * orderedReferenceWeight Q rs := by
  obtain ⟨K, T, hK, hT, hh⟩ := source_buffered_half_probabilities hinput
  refine ⟨K, T, hK, hT, ?_⟩
  intro b ρ H hH hρ hTρ hsmall F η Q hQ hF
  apply buffered_record_probability_comparison b ρ H hH hρ F (K * H / ρ)
    (div_nonneg (mul_nonneg hK (by linarith)) (by linarith)) hsmall
  · intro x hx
    exact (hh ρ H hH hρ hTρ b x hx).2
  · exact hQ
  · exact hF

end SRWTightness
