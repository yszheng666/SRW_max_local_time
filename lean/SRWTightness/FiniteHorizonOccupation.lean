import SRWTightness.FiniteHorizonWeight
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Filter

namespace SRWTightness

/-- After the actual finite exit, a finite horizon records the full occupation weight. -/
theorem finiteHorizonWeight_eq_monomial (D A : Finset Site) (v : A → ℝ)
    (n : ℕ) (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤)
    (hn : domainSteps D x ω ≤ n) :
    finiteHorizonWeight D A v n x ω = markMonomial v (killedMark D A x ω) := by
  induction n generalizing x ω with
  | zero =>
    have hx : x ∉ D := by
      intro hx
      have hh := domainSteps_first_step D x hx ω hfin
      omega
    simp only [finiteHorizonWeight, killedMark_eq_zero_of_not_mem D A x hx,
      markMonomial_zero]
  | succ n ih =>
    by_cases hx : x ∈ D
    · have hf : domainExit D (x + step (ω 0)) (shift 1 ω) ≠ ⊤ := by
        rw [domainExit_first_step D x hx ω] at hfin
        exact (WithTop.add_ne_top.mp hfin).2
      have hh := domainSteps_first_step D x hx ω hfin
      rw [finiteHorizonWeight, if_pos hx,
        ih _ _ hf (by omega), monomial_first_step D A v x hx ω hfin]
    · simp only [finiteHorizonWeight, if_neg hx,
        killedMark_eq_zero_of_not_mem D A x hx, markMonomial_zero]

/-- A positive weighted harmonic majorant proves integrability of the full killed occupation. -/
theorem integrable_monomial_of_positive_harmonic (D A : Finset Site) (v : A → ℝ)
    (hv : ∀ z, 0 ≤ v z) (F : Site → ℝ) (hF : ∀ x, 1 ≤ F x)
    (hhar : ∀ x ∈ D, F x = siteWeight A v x *
      ((1 / 4 : ℝ) * ∑ d : Direction, F (x + step d))) (x : Site) :
    Integrable (fun ω ↦ markMonomial v (killedMark D A x ω)) pathLaw := by
  let E : ℕ → Set Sample := fun n ↦ {ω | domainSteps D x ω ≤ n}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_le (measurable_domainSteps D x) measurable_const
  have hcover : AECover pathLaw atTop E := by
    refine ⟨Filter.Eventually.of_forall ?_, hE⟩
    intro ω
    exact eventually_atTop.mpr ⟨domainSteps D x ω, fun n hn ↦ hn⟩
  have he (n : ℕ) : (fun ω ↦ markMonomial v (killedMark D A x ω))
      =ᵐ[pathLaw.restrict (E n)] finiteHorizonWeight D A v n x := by
    filter_upwards [ae_restrict_of_ae (domainExit_ne_top_ae D x),
      ae_restrict_mem (hE n)] with ω hf hn
    exact (finiteHorizonWeight_eq_monomial D A v n x ω hf hn).symm
  apply hcover.integrable_of_integral_bounded_of_nonneg_ae (F x)
  · intro n
    exact (integrable_finiteHorizonWeight D A v n x).integrableOn.congr (he n).symm
  · exact Filter.Eventually.of_forall (fun ω ↦ markMonomial_nonneg v hv _)
  · apply Filter.Eventually.of_forall
    intro n
    rw [integral_congr_ae (he n)]
    exact (setIntegral_le_integral (integrable_finiteHorizonWeight D A v n x)
      (Filter.Eventually.of_forall (finiteHorizonWeight_nonneg D A v hv n x))).trans
      (finiteHorizonWeight_integral_le D A v hv F hF hhar n x)

end SRWTightness
