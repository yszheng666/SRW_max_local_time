import SRWTightness.AnnulusFineLogarithm
import SRWTightness.AnnulusEscapeEvent

namespace SRWTightness

/-- Source (2.10), with uniform numerator error and zero denominator error. -/
theorem source_annulus_probability_formula (hinput : PotentialKernelAsymptoticInput) :
    ∃ K a₀ : ℝ, 0 ≤ K ∧ 2 ≤ a₀ ∧ ∀ a R : ℝ, a₀ ≤ a → a < R →
      ∀ b x : Site, a ^ 2 < normSq (x - b) → normSq (x - b) < R ^ 2 →
        ∃ ε : ℝ, |ε| ≤ K / a ∧
          pathLaw.real {ω | domainExit (translateFinset b (diskFinset R)) x ω <
            setHittingTime (translateFinset b (diskFinset a)) x 0 ω} =
            (Real.log (Real.sqrt (normSq (x - b)) / a) + ε) / Real.log (R / a) := by
  obtain ⟨K, a₀, hK, ha₀, hh⟩ := annulus_log_formula hinput
  refine ⟨K, a₀, hK, ha₀, ?_⟩
  intro a R ha hR b x hxl hxu
  obtain ⟨ε, he, hp⟩ := hh a R ha hR (x - b) hxl.le hxu.le
  refine ⟨ε, he, ?_⟩
  rw [translated_annulus_escape_probability a R (by linarith) hR.le b x]
  exact hp

end SRWTightness
