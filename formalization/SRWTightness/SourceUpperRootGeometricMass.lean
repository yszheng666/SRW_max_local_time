import SRWTightness.SourceUpperBlockRootCount

open Filter MeasureTheory

namespace SRWTightness

/-- The actual root count retains the geometric return factor needed by the principal kernel. -/
theorem source_upper_root_count_geometric_tail (hinput : PotentialKernelAsymptoticInput) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ n : ℕ,
      pathLaw.real {ω | n + 1 ≤ sourceUpperBlockRootCount t b ω} ≤
        (1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ n := by
  obtain ⟨K, hK, hreturn⟩ := source_upper_selected_root_return_rate hinput
  refine ⟨K, hK, ?_⟩
  filter_upwards [hreturn, source_upper_block_domain_geometry,
    source_upper_block_root_coarse_range] with t hr hg hk
  intro b hb n
  have hgeom := hg (sourceUpperBlockRoot t b) (hk b hb) b hb
  have hden : 1 ≤ (sourceUpperBlockRoot t b : ℝ) + K := by
    linarith [Nat.cast_nonneg (α := ℝ) (sourceUpperBlockRoot t b)]
  have hρ : 0 ≤ 1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K) := by
    have hh := (div_le_one (by linarith : 0 < (sourceUpperBlockRoot t b : ℝ) + K)).mpr hden
    linarith
  have hh := killedChildIntervals_count_tail (diskFinset (Real.exp t))
    (sourceUpperBlockInner t (sourceUpperBlockRoot t b) b)
    (sourceUpperBlockOuter t (sourceUpperBlockRoot t b) b) hgeom.1 hgeom.2
    (1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) hρ (hr b hb) n 0
  have hp : setHitProbability (diskFinset (Real.exp t))
      (sourceUpperBlockInner t (sourceUpperBlockRoot t b) b) 0 ≤ 1 := by
    rw [setHitProbability_eq_probability]
    exact measureReal_le_one
  exact hh.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hp (pow_nonneg hρ n))

/-- Every actual root-count atom is bounded by the geometric weight, including the zero atom. -/
theorem source_upper_root_count_geometric_mass (hinput : PotentialKernelAsymptoticInput) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ J : ℕ,
      pathLaw {ω | sourceUpperBlockRootCount t b ω = J} ≤
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) := by
  obtain ⟨K, hK, ht⟩ := source_upper_root_count_geometric_tail hinput
  refine ⟨K, hK, ?_⟩
  filter_upwards [ht] with t ht
  intro b hb J
  by_cases hJ : J = 0
  · subst J
    simp only [Nat.zero_sub, pow_zero, ENNReal.ofReal_one]
    exact prob_le_one
  · rw [← ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    have hh := ht b hb (J - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ J)] at hh
    apply le_trans _ hh
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    change sourceUpperBlockRootCount t b ω = J at hω
    change J ≤ sourceUpperBlockRootCount t b ω
    omega

end SRWTightness
