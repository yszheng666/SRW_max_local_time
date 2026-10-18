import SRWTightness.ChildIntervalExtraction
import SRWTightness.Capacity

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- Standard last-visit counting for a finite killed walk. Each completed K-to-C excursion has
one last visit to K before its C-exit; testing that future at ordinary visits gives this identity.
There is no source scale, reference mixture, two-point assumption or source mean bound here. -/
def FiniteLastVisitCountInput : Prop :=
  ∀ (D K C : Finset Site), K ⊆ C → C ⊆ D → ∀ x : Site,
    Integrable (fun ω ↦ ((killedChildIntervals D K C x ω).length : ℝ)) pathLaw ∧
    (∫ ω, ((killedChildIntervals D K C x ω).length : ℝ) ∂pathLaw) =
      ∑ y ∈ K, killedGreen D x y * equilibriumMeasure C K y

end SRWTightness
