import SRWTightness.SourceEarlyPairShellBound

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- Candidate pairs in a bounded range of natural distance indices; zero includes all
macroscopic separations whose real logarithmic distance index is negative. -/
noncomputable def sourceFixedDistancePairs (t : ℝ) (a₀ : ℕ) : Finset (Site × Site) :=
  ((sourceCandidateAnnulus (Real.exp t)).product (sourceCandidateAnnulus (Real.exp t))).filter
    (fun p ↦ p.1 ≠ p.2 ∧
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))) ≤ a₀)

/-- A pointwise inverse fourth-power bound cancels the square of the annulus count. -/
theorem source_fixed_pair_sum_bound (t A γ C N : ℝ) (I a₀ : ℕ)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hcount : ((sourceCandidateAnnulus (Real.exp t)).card : ℝ) ≤ N * (Real.exp t) ^ 2)
    (hp : ∀ b w, b ∈ sourceCandidateAnnulus (Real.exp t) →
      w ∈ sourceCandidateAnnulus (Real.exp t) → b ≠ w →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) ≤ a₀ →
      sourceEnlargedLaw.real
        (sourceCenteredSuccessEvent t A γ b I ∩ sourceCenteredSuccessEvent t A γ w I) ≤
        C / (Real.exp t) ^ 4) :
    (∑ p ∈ sourceFixedDistancePairs t a₀, sourceEnlargedLaw.real
      (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I)) ≤
      N ^ 2 * C := by
  classical
  have hcard : ((sourceFixedDistancePairs t a₀).card : ℝ) ≤
      ((sourceCandidateAnnulus (Real.exp t)).card : ℝ) ^ 2 := by
    have hh : (sourceFixedDistancePairs t a₀).card ≤
        (sourceCandidateAnnulus (Real.exp t)).card ^ 2 := by
      calc
        _ ≤ ((sourceCandidateAnnulus (Real.exp t)).product
            (sourceCandidateAnnulus (Real.exp t))).card :=
          Finset.card_filter_le _ _
        _ = _ := by simp [pow_two]
    exact_mod_cast hh
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
  calc
    _ ≤ ∑ p ∈ sourceFixedDistancePairs t a₀, C / (Real.exp t) ^ 4 := by
      apply Finset.sum_le_sum
      intro p hp'
      obtain ⟨hmem, hne, ha⟩ := Finset.mem_filter.mp hp'
      obtain ⟨hb, hw⟩ := Finset.mem_product.mp hmem
      exact hp p.1 p.2 hb hw hne ha
    _ = ((sourceFixedDistancePairs t a₀).card : ℝ) * (C / (Real.exp t) ^ 4) := by
      simp
    _ ≤ (N * (Real.exp t) ^ 2) ^ 2 * (C / (Real.exp t) ^ 4) :=
      mul_le_mul_of_nonneg_right (hcard.trans hsquare) (by positivity)
    _ = _ := by field_simp

end SRWTightness
