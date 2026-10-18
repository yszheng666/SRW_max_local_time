import SRWTightness.SourceUpperAnnulusReduction
import SRWTightness.SourceUpperRootCap

open Filter MeasureTheory

namespace SRWTightness

/-- A block succeeds with exactly the indicated number of roots. -/
def sourceUpperFixedRootSuccess (t s : ℝ) (b : Site) (j : ℕ) : Set Sample :=
  {ω | sourceUpperBlockRootCount t b ω = j ∧ ω ∈ sourceUpperBlockSuccess t s b}

/-- Annulus success decomposes into crossings, root-cap failure, and positive capped root counts. -/
theorem source_upper_annulus_root_reduction (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      sourceUpperAnnulusHighEvent t s ≤ᵐ[pathLaw]
        ((sourceUpperCrossingEvent t s ∪ sourceUpperRootCapEvent t) ∪
          ⋃ b ∈ sourceUpperBlockCenters t, ⋃ j ∈ Finset.Icc 1 ⌊t ^ 2⌋₊,
            sourceUpperFixedRootSuccess t s b j : Set Sample) := by
  filter_upwards [source_upper_annulus_success_reduction hF,
    source_upper_block_success_iff_ae, eventually_ge_atTop (1 : ℝ)] with t ha he ht
  intro s hs hslog
  have hh := ae_all_iff.mpr (fun b : sourceUpperBlockCenters t ↦ he b b.property)
  filter_upwards [ha, hh] with ω hω hforest
  intro hhigh
  rcases hω s hhigh with hcross | ⟨b, hb, hsucc⟩
  · exact Or.inl (Or.inl hcross)
  by_cases hcap : t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)
  · apply Or.inl ∘ Or.inr
    simp only [sourceUpperRootCapEvent, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨b, hb, hcap⟩
  apply Or.inr
  have hj : 1 ≤ sourceUpperBlockRootCount t b ω := by
    have h := source_upper_forest_success_length_pos t s b
      (source_upper_visit_cutoff_pos t s (by linarith) hs hslog) _
      ((hforest ⟨b, hb⟩ s).mp hsucc)
    simpa only [sourceUpperBlockForest_length] using h
  have hjhi : sourceUpperBlockRootCount t b ω ≤ ⌊t ^ 2⌋₊ :=
    (Nat.le_floor_iff (sq_nonneg t)).mpr (le_of_not_gt hcap)
  simp only [Set.mem_iUnion]
  exact ⟨b, hb, sourceUpperBlockRootCount t b ω,
    Finset.mem_Icc.mpr ⟨hj, hjhi⟩, rfl, hsucc⟩

/-- The annulus upper probability reduces to the two exceptional events and finite root sums. -/
theorem source_upper_annulus_root_probability (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      pathLaw (sourceUpperAnnulusHighEvent t s) ≤
        pathLaw (sourceUpperCrossingEvent t s) + pathLaw (sourceUpperRootCapEvent t) +
          ∑ b ∈ sourceUpperBlockCenters t, ∑ j ∈ Finset.Icc 1 ⌊t ^ 2⌋₊,
            pathLaw (sourceUpperFixedRootSuccess t s b j) := by
  filter_upwards [source_upper_annulus_root_reduction hF] with t ht
  intro s hs hslog
  apply (measure_mono_ae (ht s hs hslog)).trans
  apply (measure_union_le _ _).trans
  apply add_le_add (measure_union_le _ _)
  apply (measure_biUnion_finset_le _ _).trans
  exact Finset.sum_le_sum (fun b _ ↦ measure_biUnion_finset_le _ _)

end SRWTightness
