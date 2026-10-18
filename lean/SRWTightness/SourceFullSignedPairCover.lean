import SRWTightness.SourceFullPairCover
import SRWTightness.SourceLiteralDistanceRanges
import SRWTightness.SourceCommonSignedLevel

open Filter

namespace SRWTightness

/-- The five actual candidate-pair ranges retain the signed floor, including negative indices. -/
theorem source_full_signed_pair_cover :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (I a₀ : ℕ), 0 < A → 0 < a₀ →
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ p ∈ (sourceCandidateAnnulus (Real.exp t)).product
        (sourceCandidateAnnulus (Real.exp t)),
      p ∈ sourceClosePairs (sourceCandidateAnnulus (Real.exp t)) A ∨
      p ∈ sourceLatePairs (sourceCandidateAnnulus (Real.exp t)) A I ∨
      (∃ j ∈ sourceCommonLevels t, (j : ℤ) =
        sourceSignedCommonPairLevel t (Real.sqrt (normSq (p.2 - p.1)))) ∨
      (p.1 ≠ p.2 ∧ sourceSignedDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))) ≤
        (a₀ : ℤ)) ∨
      ((a₀ : ℤ) ≤ sourceSignedDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))) ∧
        sourceSignedDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))) <
          ((sourceCoarseLowerLevel t + sourceCommonPairGap t : ℕ) : ℤ)) := by
  filter_upwards [source_full_pair_cover, sourceCoarseLowerLevel_eventually_twenty,
    eventually_ge_atTop (1 : ℝ)] with t hh hc ht
  intro A I a₀ hA ha₀ hI p hp
  rcases hh A I a₀ hA hI p hp with hclose | hlate | hcommon | hfixed | hearly
  · exact Or.inl hclose
  · exact Or.inr (Or.inl hlate)
  · obtain ⟨j, hj, hpj⟩ := hcommon
    have he := (Finset.mem_filter.mp hpj).2.2
    have hl := (Finset.mem_filter.mp hj).2
    have hn : 0 < sourceCommonPairDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))) := by
      omega
    have hz := source_signed_distance_eq_natural t (Real.sqrt (normSq (p.2 - p.1))) hn
    have hg := source_common_pair_gap_integer t ht
    refine Or.inr (Or.inr (Or.inl ⟨j, hj, ?_⟩))
    unfold sourceSignedCommonPairLevel
    rw [hz]
    omega
  · obtain ⟨_, hne, ha⟩ := Finset.mem_filter.mp hfixed
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hne,
      (source_bounded_signed_distance_iff t _ a₀).mpr ha⟩)))
  · obtain ⟨a, ha, hpa⟩ := hearly
    obtain ⟨hal, hau⟩ := Finset.mem_Ico.mp ha
    have he := (Finset.mem_filter.mp hpa).2.2
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    apply (source_signed_early_range_iff t _ a₀ _ ha₀).mpr
    constructor <;> omega

end SRWTightness
