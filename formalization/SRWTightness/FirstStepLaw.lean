import SRWTightness.FutureIndependence
import SRWTightness.ShiftHistory
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory

namespace SRWTightness

 theorem first_direction_indep_future : IndepFun (fun ω : Sample ↦ ω 0) (shift 1) pathLaw :=
  indep_of_indep_of_le_left (history_indep_future 1)
    (measurable_direction_history (by decide : 0 < 1)).comap_le

 theorem first_step_future_law :
    pathLaw.map (fun ω : Sample ↦ (ω 0, shift 1 ω)) = directionLaw.prod pathLaw := by
  have h := first_direction_indep_future.map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable (measurable_shift 1).aemeasurable
  simpa only [direction_marginal, shift_law] using h

 theorem integral_first_step_future (f : Direction → Sample → ℝ)
    (hm : ∀ d, Measurable (f d)) (hf : ∀ d, Integrable (f d) pathLaw) :
    ∫ ω, f (ω 0) (shift 1 ω) ∂pathLaw = ∫ d, ∫ ω, f d ω ∂pathLaw ∂directionLaw := by
  have hmeas : Measurable (fun p : Direction × Sample ↦ f p.1 p.2) :=
    measurable_from_prod_countable_right hm
  have hprod : Integrable (fun p : Direction × Sample ↦ f p.1 p.2)
      (directionLaw.prod pathLaw) :=
    (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hf, Integrable.of_finite⟩
  calc
    _ = ∫ p, f p.1 p.2 ∂pathLaw.map (fun ω : Sample ↦ (ω 0, shift 1 ω)) :=
      (integral_map ((measurable_pi_apply 0).prodMk (measurable_shift 1)).aemeasurable
        hmeas.aestronglyMeasurable).symm
    _ = ∫ p, f p.1 p.2 ∂directionLaw.prod pathLaw := by rw [first_step_future_law]
    _ = _ := integral_prod _ hprod

end SRWTightness
