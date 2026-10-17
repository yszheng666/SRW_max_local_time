import SRWTightness.ExternalKilledTraceFactorization
import SRWTightness.ExternalPositiveHarmonic
import SRWTightness.ExitPayoff
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
namespace SRWTightness

/-- The prescribed exit-atom probability is the actual indicator boundary payoff. -/
theorem trace_exit_probability_eq_payoff (D : Finset Site) (x e : Site) :
    traceExitProbability D x e = exitPayoff D (fun y ↦ if y = e then 1 else 0) x := by
  classical
  have hs : MeasurableSet {ω | domainExitLocation D x ω = e} :=
    (measurable_domainExitLocation D x) (Set.to_countable {e}).measurableSet
  symm
  simpa [traceExitProbability, exitPayoff, Set.indicator] using
    (integral_indicator_one (μ := pathLaw) hs)

/-- Exit-atom probabilities are harmonic inside the actual killed domain. -/
theorem trace_exit_probability_harmonic (D : Finset Site) (e x : Site) (hx : x ∈ D) :
    traceExitProbability D x e =
      (1 / 4 : ℝ) * ∑ d : Direction, traceExitProbability D (x + step d) e := by
  simp_rw [trace_exit_probability_eq_payoff]
  exact exitPayoff_first_step D _ x hx

/-- The standard harmonic input controls each actual disk exit atom relatively to its center value. -/
theorem trace_exit_probability_relative (hH : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b e : Site) (A B : ℝ), 1 ≤ A → 8 * A ≤ B →
      ∀ x ∈ translateFinset b (diskFinset (2 * A)),
        |traceExitProbability (translateFinset b (diskFinset B)) x e -
          traceExitProbability (translateFinset b (diskFinset B)) b e| ≤
        C * (A / B) * traceExitProbability (translateFinset b (diskFinset B)) b e := by
  obtain ⟨C, hC, hh⟩ := hH
  refine ⟨C, hC, ?_⟩
  intro b e A B hA hB x hx
  exact hh b A B hA hB (fun y ↦ traceExitProbability (translateFinset b (diskFinset B)) y e)
    (fun _ ↦ measureReal_nonneg)
    (fun y hy ↦ trace_exit_probability_harmonic _ e y hy) x hx

end SRWTightness
