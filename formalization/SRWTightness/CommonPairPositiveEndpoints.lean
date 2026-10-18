import SRWTightness.SourceCommonPairEndpoint

namespace SRWTightness

/-- Positive population endpoints under the square-root barrier. -/
noncomputable def commonPairPositiveEndpoints (q : ℝ) : Finset ℕ :=
  (Finset.range (⌊q ^ 2 / 2⌋₊ + 1)).filter (fun k ↦ 0 < k)

/-- The finite endpoint set supplies positivity and the exact square-root height cutoff. -/
theorem commonPairPositiveEndpoints_spec (q : ℝ) (k : ℕ)
    (hk : k ∈ commonPairPositiveEndpoints q) : 1 ≤ k ∧ 2 * (k : ℝ) ≤ q ^ 2 := by
  simp only [commonPairPositiveEndpoints, Finset.mem_filter, Finset.mem_range] at hk
  have hkf : (k : ℝ) ≤ (⌊q ^ 2 / 2⌋₊ : ℝ) := by exact_mod_cast (Nat.le_of_lt_succ hk.1)
  have hf := Nat.floor_le (div_nonneg (sq_nonneg q) (by norm_num : (0 : ℝ) ≤ 2))
  exact ⟨hk.2, by linarith⟩

/-- The actual linear endpoint height permits at most a quadratic number of population states. -/
theorem commonPairPositiveEndpoints_card (q t : ℝ) (ht : 1 ≤ t)
    (hq : 0 ≤ q) (hqt : q ≤ 4 + 4 * t) :
    ((commonPairPositiveEndpoints q).card : ℝ) ≤ 33 * t ^ 2 := by
  have hc : (commonPairPositiveEndpoints q).card ≤ ⌊q ^ 2 / 2⌋₊ + 1 := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hc' : ((commonPairPositiveEndpoints q).card : ℝ) ≤ (⌊q ^ 2 / 2⌋₊ : ℝ) + 1 := by
    exact_mod_cast hc
  have hf := Nat.floor_le (div_nonneg (sq_nonneg q) (by norm_num : (0 : ℝ) ≤ 2))
  have hq8 : q ≤ 8 * t := by linarith
  nlinarith [sq_nonneg (t - 1)]

end SRWTightness
