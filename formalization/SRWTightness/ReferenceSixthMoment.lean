import SRWTightness.ReferenceCoordinateExponential
import SRWTightness.SixthMomentFromExponential

open MeasureTheory

namespace SRWTightness

/-- The actual geometric mark law has sixth moment of order alpha times Green to the fifth. -/
theorem referenceMark_sixth_moment (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (z : K) :
    Integrable (fun Y : Mark K ↦ (Y z : ℝ) ^ 6) (referenceMarkLaw D K α) ∧
    (∫ Y : Mark K, (Y z : ℝ) ^ 6 ∂referenceMarkLaw D K α) ≤
      2949120 * α * killedGreen D z z ^ 5 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hg := killedGreen_diag_ge_one D z (hKD z.property)
  have hg0 : 0 < killedGreen D z z := by linarith
  let s := 1 / (4 * killedGreen D z z)
  have hs : 0 < s := by dsimp [s]; positivity
  have he := referenceMark_coordinate_exponential_bound D K hKD α hα hcap z s hs.le le_rfl
  have hh := sixth_moment_of_exponential (referenceMarkLaw D K α)
    (fun Y : Mark K ↦ (Y z : ℝ)) ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z))
    (fun Y ↦ Nat.cast_nonneg _) s (4 * α) hs he.1 (by simpa only [mul_assoc] using he.2)
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  dsimp [s]
  field_simp
  <;> ring

end SRWTightness
