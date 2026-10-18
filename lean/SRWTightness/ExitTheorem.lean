import SRWTightness.ExitMoment
import SRWTightness.ExitProbability

open MeasureTheory

namespace SRWTightness

/-- The complete exit lemma in the manuscript, for the canonical planar SRW. -/
theorem disk_exit_lemma (R : ℝ) (hR : 1 < R) :
    (∀ᵐ ω ∂pathLaw, exitTime R ω ≠ ⊤) ∧
    Integrable (fun ω ↦ (exitSteps R ω : ℝ)) pathLaw ∧
    R ^ 2 ≤ (∫ ω, (exitSteps R ω : ℝ) ∂pathLaw) ∧
    (∫ ω, (exitSteps R ω : ℝ) ∂pathLaw) =
      (∫ ω, normSq (position ω (exitSteps R ω)) ∂pathLaw) ∧
    (∫ ω, normSq (position ω (exitSteps R ω)) ∂pathLaw) ≤ (R + 1) ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n → pathLaw.real {ω | exitTime R ω ≤ n} ≤ (n : ℝ) / R ^ 2 := by
  have hpos : 0 < R := lt_trans zero_lt_one hR
  refine ⟨exitTime_ne_top_ae hpos.le, integrable_exitSteps hpos.le,
    integral_exitSteps_ge hpos.le, integral_exitSteps_eq_normSq hpos.le, ?_, ?_⟩
  · rw [← integral_exitSteps_eq_normSq hpos.le]
    exact integral_exitSteps_le hpos.le
  · exact fun n _ ↦ prob_exit_le R hpos n

end SRWTightness
