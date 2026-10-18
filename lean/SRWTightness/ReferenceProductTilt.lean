import SRWTightness.FiniteProductTilt
import SRWTightness.ReferenceLinearTilt
import SRWTightness.IndependentMarks

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Tilting the sum of actual independent mark observations leaves independent tilted marks. -/
theorem referenceMark_product_tilt (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (4 * L)) (k : ℕ) :
    let f := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let ν := (markProductLaw D K α k).tilted (fun Y ↦ ∑ i, f (Y i))
    IsProbabilityMeasure ν ∧
    ν = Measure.pi (fun _ : Fin k ↦ (referenceMarkLaw D K α).tilted f) ∧
    iIndepFun (fun i (Y : MarkSamples K k) ↦ Y i) ν := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let f := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  have hi : Integrable (fun Y ↦ Real.exp (f Y)) (referenceMarkLaw D K α) :=
    (referenceMark_linear_exponential_bound D K hKD α hα hcap β L hL hG hsmall).1
  letI : IsProbabilityMeasure ((referenceMarkLaw D K α).tilted f) := isProbabilityMeasure_tilted hi
  have heq : (markProductLaw D K α k).tilted (fun Y ↦ ∑ i, f (Y i)) =
      Measure.pi (fun _ : Fin k ↦ (referenceMarkLaw D K α).tilted f) :=
    finite_product_tilt (fun _ : Fin k ↦ referenceMarkLaw D K α) (fun _ ↦ f)
      (fun _ ↦ by dsimp [f]; fun_prop) (fun _ ↦ hi)
  refine ⟨?_, heq, ?_⟩
  · rw [heq]
    infer_instance
  · rw [heq]
    exact iIndepFun_pi (X := fun _ Y ↦ Y) (fun _ ↦ measurable_id.aemeasurable)

end SRWTightness
