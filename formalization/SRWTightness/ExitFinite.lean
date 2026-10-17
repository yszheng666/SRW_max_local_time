import SRWTightness.StoppedExpectation
import SRWTightness.Targets
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

 theorem prob_exit_infinite_le {R : ℝ} (hR : 0 ≤ R) (N : ℕ) (hN : 0 < N) :
    pathLaw.real {ω | exitTime R ω = ⊤} ≤ (R + 1) ^ 2 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let f : Sample → ℝ := fun ω ↦ (boundedTime R N ω : ℝ) / N
  have hf : Integrable f pathLaw := (integrable_boundedTime R N).div_const _
  have hn : 0 ≤ᵐ[pathLaw] f := Filter.Eventually.of_forall
    (fun ω ↦ div_nonneg (Nat.cast_nonneg _) hNr.le)
  have hmeas := hf.measure_le_integral hn (s := {ω | exitTime R ω = ⊤}) (by
    intro ω hω
    change exitTime R ω = ⊤ at hω
    have ht : boundedTime R N ω = N := by
      have hc : (boundedTime R N ω : WithTop ℕ) = N := by
        rw [coe_boundedTime]
        simp [boundedExit, hω]
      exact_mod_cast hc
    simp [f, ht, ne_of_gt hNr])
  have hi : ∫ ω, f ω ∂pathLaw ≤ (R + 1) ^ 2 / N := by
    dsimp [f]
    rw [integral_div]
    exact div_le_div_of_nonneg_right (integral_boundedTime_le hR N) hNr.le
  have hb := hmeas.trans (ENNReal.ofReal_le_ofReal hi)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal
    (div_nonneg (sq_nonneg (R + 1)) hNr.le)] using hr

/-- The actual disk exit is almost surely finite; no exit hypothesis is assumed. -/
theorem exitTime_ne_top_ae {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂pathLaw, exitTime R ω ≠ ⊤ := by
  have hz : pathLaw.real {ω | exitTime R ω = ⊤} = 0 := by
    by_contra h
    have hp : 0 < pathLaw.real {ω | exitTime R ω = ⊤} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm h)
    obtain ⟨N, hN⟩ := exists_nat_gt ((R + 1) ^ 2 /
      pathLaw.real {ω | exitTime R ω = ⊤} + 1)
    have hNpos : (0 : ℝ) < N := by
      have := div_nonneg (sq_nonneg (R + 1)) hp.le
      linarith
    have hb := prob_exit_infinite_le hR N (by exact_mod_cast hNpos)
    have hb' := (le_div_iff₀ hNpos).mp hb
    have hlt : (R + 1) ^ 2 <
        (N : ℝ) * pathLaw.real {ω | exitTime R ω = ⊤} := by
      apply (div_lt_iff₀ hp).mp
      linarith
    nlinarith
  have hm : pathLaw {ω | exitTime R ω = ⊤} = 0 :=
    (measureReal_eq_zero_iff (μ := pathLaw) (s := {ω | exitTime R ω = ⊤})).mp hz
  rw [ae_iff]
  simpa only [not_not] using hm

 theorem exitFiniteClaim : ExitFiniteClaim := by
  intro R hR
  exact exitTime_ne_top_ae (by linarith)

end SRWTightness
