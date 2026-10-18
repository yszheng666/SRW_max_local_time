import SRWTightness.DomainExitFutureLaw
import SRWTightness.ExitPayoff
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace SRWTightness

/-- Integrable future functions stay integrable under the exact finite-domain exit product law. -/
theorem integrable_domain_exit_future_pair (C : Finset Site) (x : Site)
    (f : Site → Sample → ℝ) (hm : ∀ z, Measurable (f z))
    (hf : ∀ z, Integrable (f z) pathLaw) :
    Integrable (fun p : Site × Sample ↦ f p.1 p.2)
      ((pathLaw.map (domainExitLocation C x)).prod pathLaw) := by
  have hmeas : Measurable (fun p : Site × Sample ↦ f p.1 p.2) :=
    measurable_from_prod_countable_right hm
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hf, ?_⟩
  apply (integrable_map_measure (measurable_of_countable
    (fun z ↦ ∫ ω, ‖f z ω‖ ∂pathLaw)).aestronglyMeasurable
      (measurable_domainExitLocation C x).aemeasurable).mpr
  exact integrable_domainExit_payoff C x (fun z ↦ ∫ ω, ‖f z ω‖ ∂pathLaw)

/-- The actual restarted future is integrable when every exit-state future
function is integrable. -/
theorem integrable_domain_exit_future (C : Finset Site) (x : Site)
    (f : Site → Sample → ℝ) (hm : ∀ z, Measurable (f z))
    (hf : ∀ z, Integrable (f z) pathLaw) :
    Integrable (fun ω ↦ f (domainExitLocation C x ω) (futureAt (domainExit C x) ω)) pathLaw := by
  have hmeas : Measurable (fun p : Site × Sample ↦ f p.1 p.2) :=
    measurable_from_prod_countable_right hm
  have hpair : Measurable (fun ω ↦
      (domainExitLocation C x ω, futureAt (domainExit C x) ω)) :=
    (measurable_domainExitLocation C x).prodMk
      (measurable_futureAt (domainExit C x) (domainExit_isStoppingTime C x))
  have hi : Integrable (fun p : Site × Sample ↦ f p.1 p.2)
      (pathLaw.map (fun ω ↦ (domainExitLocation C x ω, futureAt (domainExit C x) ω))) := by
    rw [domain_exit_site_future_law]
    exact integrable_domain_exit_future_pair C x f hm hf
  exact (integrable_map_measure hmeas.aestronglyMeasurable hpair.aemeasurable).mp hi

/-- Actual finite-domain restart integrals equal the exit payoff of the ordinary future means. -/
theorem integral_domain_exit_future (C : Finset Site) (x : Site)
    (f : Site → Sample → ℝ) (hm : ∀ z, Measurable (f z))
    (hf : ∀ z, Integrable (f z) pathLaw) :
    (∫ ω, f (domainExitLocation C x ω) (futureAt (domainExit C x) ω) ∂pathLaw) =
      exitPayoff C (fun z ↦ ∫ ω, f z ω ∂pathLaw) x := by
  have hmeas : Measurable (fun p : Site × Sample ↦ f p.1 p.2) :=
    measurable_from_prod_countable_right hm
  have hpair : Measurable (fun ω ↦
      (domainExitLocation C x ω, futureAt (domainExit C x) ω)) :=
    (measurable_domainExitLocation C x).prodMk
      (measurable_futureAt (domainExit C x) (domainExit_isStoppingTime C x))
  calc
    _ = ∫ p : Site × Sample, f p.1 p.2
        ∂pathLaw.map (fun ω ↦ (domainExitLocation C x ω, futureAt (domainExit C x) ω)) :=
      (integral_map hpair.aemeasurable hmeas.aestronglyMeasurable).symm
    _ = ∫ p : Site × Sample, f p.1 p.2
        ∂(pathLaw.map (domainExitLocation C x)).prod pathLaw := by rw [domain_exit_site_future_law]
    _ = ∫ z, ∫ ω, f z ω ∂pathLaw ∂pathLaw.map (domainExitLocation C x) :=
      integral_prod _ (integrable_domain_exit_future_pair C x f hm hf)
    _ = _ := by
      rw [integral_map (measurable_domainExitLocation C x).aemeasurable
        (measurable_of_countable (fun z ↦ ∫ ω, f z ω ∂pathLaw)).aestronglyMeasurable]
      rfl

end SRWTightness
