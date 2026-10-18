import SRWTightness.LatticeCloseNeighbors
import SRWTightness.BoundedNeighborPairs
import SRWTightness.SourceSuccessCount

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- The exact bounded-distance ordered pair contribution, including the diagonal. -/
noncomputable def sourceClosePairContribution (R A γ : ℝ)
    (I : sourceCandidateAnnulus R → ℕ)
    (z : ∀ b : sourceCandidateAnnulus R,
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))) : ℝ :=
  ∑ b : sourceCandidateAnnulus R,
    ∑ w ∈ latticeCloseNeighbors (sourceCandidateAnnulus R) A b,
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b) ∩
          sourceSiteSuccessEvent (Real.log R) A γ w (I w) (z w))

/-- Bounded-distance pairs are controlled by the actual manuscript first moment. -/
theorem source_close_pair_first_moment (R A γ : ℝ)
    (I : sourceCandidateAnnulus R → ℕ)
    (z : ∀ b : sourceCandidateAnnulus R,
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (hs : ∀ b : sourceCandidateAnnulus R,
      NullMeasurableSet (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b))
        sourceEnlargedLaw) :
    sourceClosePairContribution R A γ I z ≤
      ((diskFinset (|A| + 1)).card : ℝ) *
        (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) := by
  exact bounded_neighbor_pair_first_moment sourceEnlargedLaw Finset.univ
    (fun b : sourceCandidateAnnulus R ↦ sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b))
    (fun b _ ↦ hs b) (latticeCloseNeighbors (sourceCandidateAnnulus R) A)
    (diskFinset (|A| + 1)).card
    (fun b _ ↦ lattice_close_neighbors_card (sourceCandidateAnnulus R) A b)

end SRWTightness
