import SRWTightness.MarkTest
import SRWTightness.ReferenceIntegral
import SRWTightness.CapacityMonotone

open MeasureTheory

namespace SRWTightness

def restrictMark {K L : Finset Site} (hKL : K ⊆ L) (Y : Mark L) : Mark K :=
  fun z ↦ Y ⟨z, hKL z.property⟩

 theorem measurable_restrictMark {K L : Finset Site} (hKL : K ⊆ L) :
    Measurable (restrictMark hKL) :=
  measurable_pi_lambda _ (fun z ↦ measurable_pi_apply (⟨z, hKL z.property⟩ : L))

 theorem integrable_bounded_mark_test (K : Finset Site) (μ : Measure (Mark K)) [IsFiniteMeasure μ]
    (F : Mark K → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ Y, ‖F Y‖ ≤ C) : Integrable F μ :=
  ⟨hF.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hC)⟩

 theorem integral_reference_centered (D K : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (F : Mark K → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ Y, ‖F Y‖ ≤ C) :
    ∫ Y, F Y ∂referenceMarkLaw D K α = F 0 + α *
      ∑ x ∈ K, equilibriumMeasure D K x * (markTestExpectation D K F x - F 0) := by
  rw [integral_referenceMark D K α hα hcap F
    (fun x _ ↦ integrable_bounded_mark_test K _ F hF C hC)]
  have hi (x : Site) : (∫ Y, F Y ∂killedMarkLaw D K x) = markTestExpectation D K F x :=
    integral_map (measurable_killedMark D K x).aemeasurable hF.aestronglyMeasurable
  simp_rw [hi, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  change (1 - α * capacity D K) * F 0 +
    (∑ x ∈ K, α * equilibriumMeasure D K x * markTestExpectation D K F x) =
    F 0 + α * ((∑ x ∈ K, equilibriumMeasure D K x * markTestExpectation D K F x) - capacity D K * F 0)
  have he : (∑ x ∈ K, α * equilibriumMeasure D K x * markTestExpectation D K F x) =
      α * ∑ x ∈ K, equilibriumMeasure D K x * markTestExpectation D K F x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he]
  ring

 theorem referenceMark_restriction_integral (D K L : Finset Site) (hKL : K ⊆ L)
    (hLD : L ⊆ D) (α : ℝ) (hα : 0 ≤ α) (hcapL : α * capacity D L ≤ 1)
    (F : Mark K → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ Y, ‖F Y‖ ≤ C) :
    (∫ Y, F (restrictMark hKL Y) ∂referenceMarkLaw D L α) =
      ∫ Y, F Y ∂referenceMarkLaw D K α := by
  have hcapK : α * capacity D K ≤ 1 :=
    (mul_le_mul_of_nonneg_left (capacity_mono_set D K L hKL hLD) hα).trans hcapL
  have hFm : Measurable (fun Y : Mark L ↦ F (restrictMark hKL Y)) := hF.comp (measurable_restrictMark hKL)
  rw [integral_reference_centered D L α hα hcapL (fun Y : Mark L ↦ F (restrictMark hKL Y)) hFm
      C (fun Y ↦ hC _), integral_reference_centered D K α hα hcapK F hF C hC]
  change F 0 + α * (∑ x ∈ L, equilibriumMeasure D L x * (markTestExpectation D K F x - F 0)) = _
  rw [equilibrium_sweep D K L hKL hLD (fun x ↦ markTestExpectation D K F x - F 0)
    (fun x hx ↦ by rw [markTestExpectation_eq_of_not_mem D K F x hx, sub_self])
    (fun x hx hxK ↦ centered_markTest_harmonic D K F hF C hC x hx hxK)]

end SRWTightness
