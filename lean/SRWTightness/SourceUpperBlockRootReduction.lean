import SRWTightness.SourceUpperAnnulusRootReduction

open Filter MeasureTheory

namespace SRWTightness

/-- Each actual successful block has either an excessive root count or a positive capped count. -/
theorem source_upper_block_root_reduction :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      sourceUpperBlockSuccess t s b ≤ᵐ[pathLaw]
        ({ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)} ∪
          ⋃ J ∈ Finset.Icc 1 ⌊t ^ 2⌋₊, sourceUpperFixedRootSuccess t s b J : Set Sample) := by
  filter_upwards [source_upper_block_success_iff_ae, eventually_ge_atTop (1 : ℝ)]
    with t he ht
  intro b hb s hs hslog
  filter_upwards [he b hb] with ω hω
  intro hsucc
  by_cases hcap : t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)
  · exact Or.inl hcap
  apply Or.inr
  have hj : 1 ≤ sourceUpperBlockRootCount t b ω := by
    have h := source_upper_forest_success_length_pos t s b
      (source_upper_visit_cutoff_pos t s (by linarith) hs hslog) _ ((hω s).mp hsucc)
    simpa only [sourceUpperBlockForest_length] using h
  have hjhi : sourceUpperBlockRootCount t b ω ≤ ⌊t ^ 2⌋₊ :=
    (Nat.le_floor_iff (sq_nonneg t)).mpr (le_of_not_gt hcap)
  simp only [Set.mem_iUnion]
  exact ⟨sourceUpperBlockRootCount t b ω, Finset.mem_Icc.mpr ⟨hj, hjhi⟩, rfl, hsucc⟩

/-- Untruncated block success probabilities are bounded by the individual cap tails and capped sums. -/
theorem source_upper_block_root_probability_sum :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      (∑ b ∈ sourceUpperBlockCenters t, pathLaw (sourceUpperBlockSuccess t s b)) ≤
        (∑ b ∈ sourceUpperBlockCenters t,
          pathLaw {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)}) +
        ∑ b ∈ sourceUpperBlockCenters t, ∑ J ∈ Finset.Icc 1 ⌊t ^ 2⌋₊,
          pathLaw (sourceUpperFixedRootSuccess t s b J : Set Sample) := by
  filter_upwards [source_upper_block_root_reduction] with t ht
  intro s hs hslog
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b hb
  apply (measure_mono_ae (ht b hb s hs hslog)).trans
  apply (measure_union_le _ _).trans
  exact add_le_add le_rfl (measure_biUnion_finset_le _ _)

end SRWTightness
