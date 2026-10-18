import SRWTightness.StoppedExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Source equation (2.2), for the original SRW rather than an assumed exit law. -/
theorem prob_exit_le (R : ℝ) (hR : 0 < R) (N : ℕ) :
    pathLaw.real {ω | exitTime R ω ≤ N} ≤ (N : ℝ) / R ^ 2 := by
  let f : Sample → ℝ := fun ω ↦ normSq (position ω (boundedTime R N ω)) / R ^ 2
  have hf : Integrable f pathLaw := (integrable_normSq_boundedTime R N).div_const _
  have hn : 0 ≤ᵐ[pathLaw] f := Filter.Eventually.of_forall
    (fun ω ↦ div_nonneg (normSq_nonneg _) (sq_nonneg _))
  have hmeas := hf.measure_le_integral hn (s := {ω | exitTime R ω ≤ N}) (by
    intro ω hω
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    simpa only [one_mul] using normSq_at_boundedTime_ge_on_exit R N ω hω)
  have ht : ∫ ω, (boundedTime R N ω : ℝ) ∂pathLaw ≤ N := by
    calc
      _ ≤ ∫ _ : Sample, (N : ℝ) ∂pathLaw :=
        integral_mono (integrable_boundedTime R N) (integrable_const _)
          (fun ω ↦ Nat.cast_le.mpr (boundedTime_le R N ω))
      _ = N := by simp
  have hi : ∫ ω, f ω ∂pathLaw ≤ (N : ℝ) / R ^ 2 := by
    dsimp [f]
    rw [integral_div, integral_normSq_boundedTime_eq]
    exact div_le_div_of_nonneg_right ht (sq_nonneg _)
  have hb := hmeas.trans (ENNReal.ofReal_le_ofReal hi)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal
    (div_nonneg (Nat.cast_nonneg N) (sq_nonneg R))] using hr

end SRWTightness
