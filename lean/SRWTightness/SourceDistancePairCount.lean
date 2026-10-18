import SRWTightness.SourceEarlyDistanceUpper
import SRWTightness.LatticePairCount
import SRWTightness.SourceCandidateAnnulus

open Filter
namespace SRWTightness

/-- Distinct ordered candidate pairs with a specified distance index. -/
noncomputable def sourceDistancePairs (Z : Finset Site) (t : ℝ) (j : ℕ) : Finset (Site × Site) := by
  classical
  exact (Z.product Z).filter (fun p ↦ p.1 ≠ p.2 ∧
    j = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))))

/-- Positive distance-index shells have the source exponential spatial counting radius. -/
theorem source_distance_pairs_card (hDisk : LatticeDiskCountInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (Z : Finset Site) (j : ℕ), 1 ≤ j →
      ((sourceDistancePairs Z t j).card : ℝ) ≤
        C * Z.card * Real.exp (2 * t - 2 * (j : ℝ)) := by
  classical
  obtain ⟨C, hC, hc⟩ := lattice_nearby_pairs_quadratic hDisk
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_early_distance_upper] with t ht
  intro Z j hj
  let a := Real.exp (t - (j : ℝ))
  by_cases hn : (sourceDistancePairs Z t j).Nonempty
  · obtain ⟨p, hp⟩ := hn
    obtain ⟨_, hbw, hi⟩ := Finset.mem_filter.mp hp
    have ha : 1 ≤ a := (ht p.1 p.2 j hj hbw hi).1.trans
      (ht p.1 p.2 j hj hbw hi).2
    have hsub : sourceDistancePairs Z t j ⊆ latticeNearbyPairs Z a := by
      intro q hq
      obtain ⟨hZ, hne, hindex⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hZ, (ht q.1 q.2 j hj hne hindex).2⟩
    have hcard : ((sourceDistancePairs Z t j).card : ℝ) ≤ (latticeNearbyPairs Z a).card := by
      exact_mod_cast Finset.card_le_card hsub
    have he : a ^ 2 = Real.exp (2 * t - 2 * (j : ℝ)) := by
      dsimp [a]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [he] using hcard.trans (hc Z a ha)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Equation 8.26 for every positive distance index, including all moving early distances. -/
theorem source_distance_pairs_annulus_card (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, 1 ≤ j →
      ((sourceDistancePairs (sourceCandidateAnnulus (Real.exp t)) t j).card : ℝ) ≤
        C * Real.exp (4 * t - 2 * (j : ℝ)) := by
  obtain ⟨C, hC, hc⟩ := source_distance_pairs_card hDisk
  obtain ⟨c, B, hc0, hB, hband⟩ := hAnnulus
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  filter_upwards [hc, Real.tendsto_exp_atTop.eventually hband] with t ht hband
  intro j hj
  have hh := (ht (sourceCandidateAnnulus (Real.exp t)) j hj).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hband.2 hC.le)
      (Real.exp_nonneg _))
  have he : C * (B * Real.exp t ^ 2) *
      Real.exp (2 * t - 2 * (j : ℝ)) =
      C * B * Real.exp (4 * t - 2 * (j : ℝ)) := by
    rw [pow_two]
    rw [show C * (B * (Real.exp t * Real.exp t)) * Real.exp
        (2 * t - 2 * (j : ℝ)) =
      (C * B) * ((Real.exp t * Real.exp t) * Real.exp
        (2 * t - 2 * (j : ℝ))) by ring]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  exact he ▸ hh

end SRWTightness
