import SRWTightness.SourceFarPairSplit
import SRWTightness.SourcePairShellCover
import SRWTightness.SourceFixedPairSumBound
import SRWTightness.SourceCommonPairCount

open Filter
namespace SRWTightness

/-- The close candidate pairs, including the diagonal. -/
noncomputable def sourceClosePairs (Z : Finset Site) (A : ℝ) : Finset (Site × Site) :=
  (Z.product Z).filter (fun p ↦ Real.sqrt (normSq (p.2 - p.1)) ≤ A)

/-- Every candidate pair belongs to one of the five estimated distance ranges. -/
theorem source_full_pair_cover :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (I a₀ : ℕ), 0 < A →
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ p ∈ (sourceCandidateAnnulus (Real.exp t)).product
        (sourceCandidateAnnulus (Real.exp t)),
      p ∈ sourceClosePairs (sourceCandidateAnnulus (Real.exp t)) A ∨
      p ∈ sourceLatePairs (sourceCandidateAnnulus (Real.exp t)) A I ∨
      (∃ j ∈ sourceCommonLevels t,
        p ∈ sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j) ∨
      p ∈ sourceFixedDistancePairs t a₀ ∨
      (∃ a ∈ Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t),
        p ∈ sourceDistancePairs (sourceCandidateAnnulus (Real.exp t)) t a) := by
  classical
  filter_upwards [source_far_pair_split] with t ht
  intro A I a₀ hA hI p hp
  by_cases hc : Real.sqrt (normSq (p.2 - p.1)) ≤ A
  · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hc⟩)
  have hsep : A < Real.sqrt (normSq (p.2 - p.1)) := lt_of_not_ge hc
  by_cases hl : Real.sqrt (normSq (p.2 - p.1)) ≤
      A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio)
  · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hp, hsep, hl⟩))
  have hne : p.1 ≠ p.2 := by
    intro he
    have hh : p.2 - p.1 = 0 := sub_eq_zero.mpr he.symm
    simp only [hh, normSq, Real.sqrt_zero] at hsep
    norm_num at hsep
    linarith
  rcases ht A I p.1 p.2 hA hne hI (lt_of_not_ge hl) with hj | ha
  · obtain ⟨j, hj, he⟩ := hj
    exact Or.inr (Or.inr (Or.inl ⟨j, hj, Finset.mem_filter.mpr ⟨hp, hne, he⟩⟩))
  · by_cases hf : sourceCommonPairDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))) ≤ a₀
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hp, hne, hf⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, Finset.mem_Ico.mpr ⟨by omega, ha⟩,
        Finset.mem_filter.mpr ⟨hp, hne, rfl⟩⟩)))

end SRWTightness
