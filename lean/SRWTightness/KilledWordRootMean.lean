import SRWTightness.WordMark
import SRWTightness.FiniteLastVisitCountInput

open MeasureTheory
namespace SRWTightness

/-- The actual root-count functional is integrable under a killed ordered-word law. -/
theorem integrable_killedWordMark_roots (hLast : FiniteLastVisitCountInput)
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) :
    Integrable (fun Y ↦ (wordMarkRootCount K C Y : ℝ)) (killedWordMarkLaw D x) := by
  have hm : Measurable (fun Y : WordMark ↦ (wordMarkRootCount K C Y : ℝ)) :=
    measurable_of_countable _
  apply (integrable_map_measure hm.aestronglyMeasurable
    (measurable_killedWordMark D x).aemeasurable).mpr
  exact (hLast D K C hKC hCD x).1

/-- The finite-walk last-visit identity transfers to the root count on the ordered mark itself. -/
theorem integral_killedWordMark_roots (hLast : FiniteLastVisitCountInput)
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) :
    (∫ Y, (wordMarkRootCount K C Y : ℝ) ∂killedWordMarkLaw D x) =
      ∑ y ∈ K, killedGreen D x y * equilibriumMeasure C K y := by
  have hm : Measurable (fun Y : WordMark ↦ (wordMarkRootCount K C Y : ℝ)) :=
    measurable_of_countable _
  have hh := integral_map (μ := pathLaw) (measurable_killedWordMark D x).aemeasurable
    hm.aestronglyMeasurable
  exact hh.trans (hLast D K C hKC hCD x).2

end SRWTightness
