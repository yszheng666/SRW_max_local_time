import SRWTightness.BufferedAnnulusHalf
import SRWTightness.AnnulusEscapeEvent

namespace SRWTightness

/-- Simultaneously translating domain, target and start preserves the actual hitting probability. -/
theorem setHitProbability_translate (b : Site) (D K : Finset Site) (x : Site) :
    setHitProbability (translateFinset b D) (translateFinset b K) (b + x) =
      setHitProbability D K x := by
  rw [setHitProbability_eq_hitting, setHitProbability_eq_hitting]
  simp only [setHittingTime_translate, domainExit_translate]

/-- Source middle entrance and return layers give uniform complementary half probabilities. -/
theorem source_buffered_half_probabilities (hinput : PotentialKernelAsymptoticInput) :
    ∃ K T : ℝ, 0 ≤ K ∧ 2 ≤ T ∧ ∀ ρ H : ℝ, 1 ≤ H → 8 * H ≤ ρ → T ≤ ρ - H →
      ∀ b x : Site,
        ((Real.exp 1 * ρ - H - 1 ≤ Real.sqrt (normSq (x - b)) ∧
          Real.sqrt (normSq (x - b)) ≤ Real.exp 1 * ρ - H) ∨
        (Real.exp 1 * ρ + H ≤ Real.sqrt (normSq (x - b)) ∧
          Real.sqrt (normSq (x - b)) ≤ Real.exp 1 * ρ + H + 1)) →
        |pathLaw.real {ω | domainExit (translateFinset b (diskFinset (Real.exp 2 * ρ + H))) x ω <
          setHittingTime (translateFinset b (diskFinset (ρ - H))) x 0 ω} - 1 / 2| ≤ K * H / ρ ∧
        |setHitProbability (translateFinset b (diskFinset (Real.exp 2 * ρ + H)))
          (translateFinset b (diskFinset (ρ - H))) x - 1 / 2| ≤ K * H / ρ := by
  obtain ⟨K, T, hK, hT, hh⟩ := buffered_annulus_half hinput
  refine ⟨K, T, hK, hT, ?_⟩
  intro ρ H hH hρ hTρ b x hx
  have hbuf := middle_boundary_layers_in_buffer (Real.sqrt (normSq (x - b))) ρ H hH hx
  have hp := hh ρ H hH hρ hTρ (x - b) hbuf
  have hg := buffered_middle_annulus_geometry ρ H hH hρ (x - b) hbuf
  constructor
  · rw [translated_annulus_escape_probability (ρ - H) (Real.exp 2 * ρ + H)
      (by linarith [hg.1]) hg.2.1]
    exact hp
  · have hx' : x = b + (x - b) := by abel
    rw [hx', setHitProbability_translate]
    rw [annulusOuterExitProbability_eq_one_sub_hit] at hp
    have he : |setHitProbability (diskFinset (Real.exp 2 * ρ + H)) (diskFinset (ρ - H))
        (x - b) - 1 / 2| =
        |1 - setHitProbability (diskFinset (Real.exp 2 * ρ + H)) (diskFinset (ρ - H))
        (x - b) - 1 / 2| := by
      rw [show 1 - setHitProbability (diskFinset (Real.exp 2 * ρ + H)) (diskFinset (ρ - H))
        (x - b) - 1 / 2 = -(setHitProbability (diskFinset (Real.exp 2 * ρ + H))
        (diskFinset (ρ - H)) (x - b) - 1 / 2) by ring, abs_neg]
    exact he.trans_le hp

end SRWTightness
