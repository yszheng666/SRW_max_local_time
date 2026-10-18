import SRWTightness.ReferenceMark
import SRWTightness.EquilibriumSweep

open MeasureTheory

namespace SRWTightness

noncomputable def markTestExpectation (D K : Finset Site) (F : Mark K → ℝ) (x : Site) : ℝ :=
  ∫ ω, F (killedMark D K x ω) ∂pathLaw

 theorem integrable_markTest (D K : Finset Site) (F : Mark K → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ Y, ‖F Y‖ ≤ C) (x : Site) :
    Integrable (fun ω ↦ F (killedMark D K x ω)) pathLaw := by
  refine ⟨(hF.comp (measurable_killedMark D K x)).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C) ?_⟩
  exact Filter.Eventually.of_forall (fun ω ↦ hC _)

 theorem killedMark_eq_zero_of_not_mem (D K : Finset Site) (x : Site) (hx : x ∉ D)
    (ω : Sample) : killedMark D K x ω = 0 := by
  funext y
  exact domainLocalTime_zero_of_not_mem D x y hx ω

 theorem markTestExpectation_eq_of_not_mem (D K : Finset Site) (F : Mark K → ℝ)
    (x : Site) (hx : x ∉ D) : markTestExpectation D K F x = F 0 := by
  simp [markTestExpectation, killedMark_eq_zero_of_not_mem D K x hx]

 theorem killedMark_first_step_of_not_mem (D K : Finset Site) (x : Site) (hx : x ∈ D)
    (hxK : x ∉ K) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    killedMark D K x ω = killedMark D K (x + step (ω 0)) (shift 1 ω) := by
  funext y
  have hxy : x ≠ (y : Site) := fun h ↦ hxK (h ▸ y.property)
  change domainLocalTime D x y ω = _
  rw [domainLocalTime_first_step D x y hx ω hfin, if_neg hxy, zero_add]
  rfl

 theorem markTestExpectation_harmonic (D K : Finset Site) (F : Mark K → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ Y, ‖F Y‖ ≤ C)
    (x : Site) (hx : x ∈ D) (hxK : x ∉ K) :
    markTestExpectation D K F x = (1 / 4 : ℝ) *
      ∑ d : Direction, markTestExpectation D K F (x + step d) := by
  have he : (fun ω ↦ F (killedMark D K x ω)) =ᵐ[pathLaw]
      (fun ω ↦ F (killedMark D K (x + step (ω 0)) (shift 1 ω))) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    rw [killedMark_first_step_of_not_mem D K x hx hxK ω hω]
  unfold markTestExpectation
  rw [integral_congr_ae he, integral_first_step_future
    (fun d ω ↦ F (killedMark D K (x + step d) ω))
    (fun d ↦ hF.comp (measurable_killedMark D K _))
    (fun d ↦ integrable_markTest D K F hF C hC _)]
  exact integral_direction_average _

 theorem centered_markTest_harmonic (D K : Finset Site) (F : Mark K → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ Y, ‖F Y‖ ≤ C)
    (x : Site) (hx : x ∈ D) (hxK : x ∉ K) :
    markTestExpectation D K F x - F 0 = (1 / 4 : ℝ) *
      ∑ d : Direction, (markTestExpectation D K F (x + step d) - F 0) := by
  rw [markTestExpectation_harmonic D K F hF C hC x hx hxK, Finset.sum_sub_distrib]
  have hc : (∑ _ : Direction, F 0) = 4 * F 0 := by simp [Direction]
  rw [hc]
  ring

end SRWTightness
