import SRWTightness.SourceCommonDistanceUpper
import SRWTightness.LatticePairCount
import SRWTightness.SourceCandidateAnnulus

open Filter
namespace SRWTightness

/-- Distinct ordered candidate pairs assigned to a specified common endpoint. -/
noncomputable def sourceCommonPairs (Z : Finset Site) (t : ℝ) (j : ℕ) : Finset (Site × Site) := by
  classical
  exact (Z.product Z).filter (fun p ↦ p.1 ≠ p.2 ∧
    j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))))

/-- A common-index shell has the actual exponential spatial counting radius. -/
theorem source_common_pairs_card (hDisk : LatticeDiskCountInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (Z : Finset Site) (j : ℕ),
      ((sourceCommonPairs Z t j).card : ℝ) ≤
        C * Z.card * Real.exp (2 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ)) := by
  classical
  obtain ⟨C, hC, hc⟩ := lattice_nearby_pairs_quadratic hDisk
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_common_distance_upper] with t ht
  intro Z j
  let a := Real.exp (t - (j : ℝ) - (sourceCommonPairGap t : ℝ))
  by_cases hn : (sourceCommonPairs Z t j).Nonempty
  · obtain ⟨p, hp⟩ := hn
    obtain ⟨_, hbw, hi⟩ := Finset.mem_filter.mp hp
    have ha : 1 ≤ a := (source_common_distance_range t p.1 p.2 j hbw hi).1.trans
      (ht p.1 p.2 j hbw hi)
    have hsub : sourceCommonPairs Z t j ⊆ latticeNearbyPairs Z a := by
      intro q hq
      obtain ⟨hZ, hne, hindex⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hZ, ht q.1 q.2 j hne hindex⟩
    have hcard : ((sourceCommonPairs Z t j).card : ℝ) ≤ (latticeNearbyPairs Z a).card := by
      exact_mod_cast Finset.card_le_card hsub
    have he : a ^ 2 = Real.exp (2 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ)) := by
      dsimp [a]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [he] using hcard.trans (hc Z a ha)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The candidate annulus gives the manuscript C exp(4t-2j-2J_t) common-pair count. -/
theorem source_common_pairs_annulus_card (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ j : ℕ,
      ((sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j).card : ℝ) ≤
        C * Real.exp (4 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ)) := by
  obtain ⟨C, hC, hc⟩ := source_common_pairs_card hDisk
  obtain ⟨c, B, hc0, hB, hband⟩ := hAnnulus
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  filter_upwards [hc, Real.tendsto_exp_atTop.eventually hband] with t ht hband
  intro j
  have hh := (ht (sourceCandidateAnnulus (Real.exp t)) j).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hband.2 hC.le)
      (Real.exp_nonneg _))
  have he : C * (B * Real.exp t ^ 2) *
      Real.exp (2 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ)) =
      C * B * Real.exp (4 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ)) := by
    rw [pow_two]
    rw [show C * (B * (Real.exp t * Real.exp t)) * Real.exp
        (2 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ)) =
      (C * B) * ((Real.exp t * Real.exp t) * Real.exp
        (2 * t - 2 * (j : ℝ) - 2 * (sourceCommonPairGap t : ℝ))) by ring]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  exact he ▸ hh

end SRWTightness
