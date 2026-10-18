import SRWTightness.Filtration
import SRWTightness.IncrementMean
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace SRWTightness

/-- Conditional expectation of any one-step observable, with respect to the entire past. -/
theorem condExp_direction (n : ℕ) (f : Direction → ℝ) :
    pathLaw[fun ω : Sample ↦ f (ω n) | history n] =ᵐ[pathLaw]
      fun _ ↦ ∫ d, f d ∂directionLaw := by
  have hd : Disjoint (Finset.range n) {n} := by simp
  have h := directions_independent.indepFun_finset (Finset.range n) {n} hd
    (fun i ↦ measurable_pi_apply i)
  have hraw : IndepFun ((Finset.range n).restrict :
      Sample → (i : Finset.range n) → Direction) (fun ω ↦ ω n) pathLaw :=
    h.comp measurable_id
      (measurable_of_countable (fun w : (i : ({n} : Finset ℕ)) → Direction ↦
        w ⟨n, Finset.mem_singleton_self n⟩))
  have hind : Indep (MeasurableSpace.comap (fun ω : Sample ↦ ω n) inferInstance)
      (history n) pathLaw := hraw.symm
  have hmf : StronglyMeasurable[
      MeasurableSpace.comap (fun ω : Sample ↦ ω n) inferInstance]
      (fun ω : Sample ↦ f (ω n)) :=
    ((measurable_of_countable f).comp (comap_measurable (fun ω : Sample ↦ ω n))).stronglyMeasurable
  have hc := condExp_indep_eq (measurable_pi_apply n).comap_le (history.le n) hmf hind
  filter_upwards [hc] with ω hω
  exact hω.trans (integral_direction n f)

 theorem condExp_increment_fst (n : ℕ) :
    pathLaw[fun ω : Sample ↦ ((step (ω n)).1 : ℝ) | history n] =ᵐ[pathLaw] 0 := by
  filter_upwards [condExp_direction n (fun d ↦ ((step d).1 : ℝ))] with ω hω
  simpa only [integral_step_fst, Pi.zero_apply] using hω

 theorem condExp_increment_snd (n : ℕ) :
    pathLaw[fun ω : Sample ↦ ((step (ω n)).2 : ℝ) | history n] =ᵐ[pathLaw] 0 := by
  filter_upwards [condExp_direction n (fun d ↦ ((step d).2 : ℝ))] with ω hω
  simpa only [integral_step_snd, Pi.zero_apply] using hω

end SRWTightness
