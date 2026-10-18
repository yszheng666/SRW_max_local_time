import SRWTightness.SourceFullPairCover
import SRWTightness.NonnegativeFiniteCoverSum
import SRWTightness.SourceCenteredPairContribution
import SRWTightness.SourcePairShellSites

open MeasureTheory Filter
namespace SRWTightness

/-- Subtype-indexed ordered pairs and the finite Cartesian product give the same weighted sum. -/
theorem source_subtype_pair_sum_product (Z : Finset Site) (P : Site × Site → ℝ) :
    (∑ b : Z, ∑ w : Z, P (b, w)) = ∑ p ∈ Z.product Z, P p := by
  rw [Finset.product_eq_sprod, Finset.sum_product]
  calc
    _ = ∑ b : Z, ∑ w ∈ Z, P (b, w) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_coe_sort Z (fun w ↦ P (b, w))
    _ = _ := Finset.sum_coe_sort Z (fun b ↦ ∑ w ∈ Z, P (b, w))

/-- The canonical pair contribution equals the Cartesian-product sum over candidate sites. -/
theorem source_centered_pair_contribution_product (t A γ : ℝ) (I : ℕ) :
    sourceCenteredPairContribution t A γ I =
      ∑ p ∈ (sourceCandidateAnnulus (Real.exp t)).product
        (sourceCandidateAnnulus (Real.exp t)), sourceEnlargedLaw.real
          (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I) := by
  unfold sourceCenteredPairContribution
  exact source_subtype_pair_sum_product (sourceCandidateAnnulus (Real.exp t))
    (fun p ↦ sourceEnlargedLaw.real
      (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I))

/-- Center witnesses do not change the pair weights used in the late/common estimates. -/
theorem source_pair_success_weight_eq_centered (t A γ : ℝ) (I : ℕ)
    (z : ∀ b : Site, translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : ∀ b, (z b : Site) = b) (p : Site × Site) :
    sourcePairSuccessWeight t A γ I z p = sourceEnlargedLaw.real
      (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I) := by
  unfold sourcePairSuccessWeight
  rw [source_centered_success_event_eq t A γ p.1 I (z p.1) (hz p.1),
    source_centered_success_event_eq t A γ p.2 I (z p.2) (hz p.2)]

/-- Summing the complete geometric cover reduces every nonnegative pair weight to the five
already estimated distance contributions; no disjointness is assumed. -/
theorem source_full_pair_sum_bound :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (I a₀ : ℕ), 0 < A →
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ P : Site × Site → ℝ, (∀ p, 0 ≤ P p) →
      let Z := sourceCandidateAnnulus (Real.exp t)
      (∑ p ∈ Z.product Z, P p) ≤
        (∑ p ∈ sourceClosePairs Z A, P p) +
        (∑ p ∈ sourceLatePairs Z A I, P p) +
        (∑ j ∈ sourceCommonLevels t, ∑ p ∈ sourceCommonPairs Z t j, P p) +
        (∑ p ∈ sourceFixedDistancePairs t a₀, P p) +
        ∑ a ∈ Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t),
          ∑ p ∈ sourceDistancePairs Z t a, P p := by
  classical
  filter_upwards [source_full_pair_cover] with t ht
  intro A I a₀ hA hI P hP
  dsimp only
  let Z := sourceCandidateAnnulus (Real.exp t)
  let common := (sourceCommonLevels t).biUnion (sourceCommonPairs Z t)
  let early := (Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t)).biUnion
    (sourceDistancePairs Z t)
  have hcover : ∀ p ∈ Z.product Z,
      p ∈ sourceClosePairs Z A ∨ p ∈ sourceLatePairs Z A I ∨ p ∈ common ∨
        p ∈ sourceFixedDistancePairs t a₀ ∨ p ∈ early := by
    intro p hp
    rcases ht A I a₀ hA hI p hp with hc | hl | hcommon | hf | he
    · exact Or.inl hc
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_biUnion.mpr hcommon)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hf)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_biUnion.mpr he))))
  have hb := nonnegative_five_cover_sum_le (Z.product Z) (sourceClosePairs Z A)
    (sourceLatePairs Z A I) common (sourceFixedDistancePairs t a₀) early P hP hcover
  have hc := nonnegative_biUnion_sum_le (sourceCommonLevels t) (sourceCommonPairs Z t) P hP
  have he := nonnegative_biUnion_sum_le
    (Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t))
    (sourceDistancePairs Z t) P hP
  change (∑ p ∈ common, P p) ≤ _ at hc
  change (∑ p ∈ early, P p) ≤ _ at he
  linarith only [hb, hc, he]

end SRWTightness
