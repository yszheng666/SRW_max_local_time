import SRWTightness.ReferenceWordMark
import SRWTightness.ReferenceIntegral

open MeasureTheory
namespace SRWTightness

/-- Projecting a killed ordered word gives exactly the earlier killed occupation law. -/
theorem killedWordMarkLaw_occupation (D K : Finset Site) (x : Site) :
    (killedWordMarkLaw D x).map (wordMarkOccupation K) = killedMarkLaw D K x := by
  rw [killedWordMarkLaw, Measure.map_map (measurable_of_countable _)
    (measurable_killedWordMark D x)]
  change pathLaw.map (fun ω ↦ wordMarkOccupation K (killedWordMark D x ω)) = _
  simp only [wordMarkOccupation_killed, killedMarkLaw]

/-- The richer reference law projects exactly to the existing occupation-mark reference law. -/
theorem referenceWordMarkLaw_occupation (D K : Finset Site) (α : ℝ) :
    (referenceWordMarkLaw D K α).map (wordMarkOccupation K) = referenceMarkLaw D K α := by
  have hm : Measurable (wordMarkOccupation K) := measurable_of_countable _
  rw [referenceWordMarkLaw, Measure.map_add _ _ hm,
    Measure.map_finset_sum hm.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac, killedWordMarkLaw_occupation,
    wordMarkOccupation, referenceMarkLaw]

/-- The ordered reference law retains the constant visit intensity of its occupation projection. -/
theorem referenceWordMark_mean (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (z : K) :
    ∫ Y, (wordMarkOccupation K Y z : ℝ) ∂referenceWordMarkLaw D K α = α := by
  have hm : Measurable (wordMarkOccupation K) := measurable_of_countable _
  have hcoord : Measurable (fun Y : Mark K ↦ (Y z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z)
  have hh := integral_map (μ := referenceWordMarkLaw D K α)
    hm.aemeasurable hcoord.aestronglyMeasurable
  rw [referenceWordMarkLaw_occupation] at hh
  exact hh.symm.trans (referenceMark_mean D K hKD α hα hcap z)

end SRWTightness
