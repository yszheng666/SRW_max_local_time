import SRWTightness.CompetingEntranceLaw
import SRWTightness.ExitPayoff

open MeasureTheory
namespace SRWTightness

/-- Starting outside the target, every retained competing entrance lies on its actual one-step boundary. -/
theorem competing_boundary_support_of_not_mem (D K : Finset Site) (hKD : K ⊆ D)
    (x : Site) (hx : x ∉ K) :
    ∀ᵐ y ∂competingEntranceLaw D K x, y ∈ domainExitBoundary (D \ K) ∩ (K : Set Site) := by
  by_cases hxD : x ∈ D
  · exact competingEntranceLaw_supported_boundary D K x (Finset.mem_sdiff.mpr ⟨hxD, hx⟩)
  · change ∀ᵐ y ∂(pathLaw.map (domainExitLocation (D \ K) x)).restrict (K : Set Site),
      y ∈ domainExitBoundary (D \ K) ∩ (K : Set Site)
    rw [ae_restrict_iff' (Finset.measurableSet K)]
    apply (ae_map_iff (measurable_domainExitLocation (D \ K) x).aemeasurable
      (Set.to_countable _ |>.measurableSet)).mpr
    filter_upwards [] with ω
    intro hy
    have hnot : x ∉ D \ K := fun h ↦ hxD (Finset.mem_sdiff.mp h).1
    rw [domainExitLocation_zero_of_not_mem (D \ K) x hnot ω] at hy
    exact False.elim (hx (show x ∈ K from hy))

end SRWTightness
