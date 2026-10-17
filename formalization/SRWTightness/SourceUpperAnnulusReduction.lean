import SRWTightness.SourceUpperBlockTraversalComparison
import SRWTightness.SourceUpperBlockSuccess
import SRWTightness.SourceUpperCrossingEvent

open Filter MeasureTheory

namespace SRWTightness

/-- High local time in the source annulus inside the open half-radius disk. -/
def sourceUpperAnnulusHighEvent (t s : ℝ) : Set Sample :=
  {ω | ∃ x ∈ diskFinset (Real.exp t / 2), Real.exp t / t < Real.sqrt (normSq x) ∧
    sourceUpperVisitCutoff t s ≤ domainLocalTime (diskFinset (Real.exp t)) 0 x ω}

/-- Outside actual point-centered crossings, every high annulus site yields block success. -/
theorem source_upper_annulus_success_reduction (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      ω ∈ sourceUpperAnnulusHighEvent t s →
        ω ∈ sourceUpperCrossingEvent t s ∨
          ∃ b ∈ sourceUpperBlockCenters t, ω ∈ sourceUpperBlockSuccess t s b := by
  filter_upwards [source_upper_block_count_le_point_ae hF, source_upper_block_cover]
    with t hc hcover
  have hh := ae_all_iff.mpr (fun b : sourceUpperBlockCenters t ↦ hc b b.property)
  filter_upwards [hh] with ω hω
  intro s hs
  by_cases hcross : ω ∈ sourceUpperCrossingEvent t s
  · exact Or.inl hcross
  right
  obtain ⟨x, hx, hxlo, hhigh⟩ := hs
  have hxhi : Real.sqrt (normSq x) ≤ Real.exp t / 2 := by
    have hn := (mem_diskFinset _ _).mp hx
    exact ((Real.sqrt_lt (normSq_nonneg x) (by positivity)).mpr hn).le
  obtain ⟨b, hb, hxb⟩ := hcover x hxlo hxhi
  refine ⟨b, hb, ⟨⟨⟨x, hxb⟩, hhigh⟩, ?_⟩⟩
  intro j hj hJ
  have hpoint : Real.sqrt (2 * (sourceUpperTraversalCount t j x ω : ℝ)) ≤
      sourceUpperBarrier t s j := by
    apply le_of_not_gt
    intro hgt
    apply hcross
    simp only [sourceUpperCrossingEvent, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨x, hx, j, Finset.mem_range.mpr (by omega), hgt⟩
  have hn := hω ⟨b, hb⟩ j hj.le hJ x hxb
  exact (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (show (sourceUpperBlockCount t b j ω : ℝ) ≤ sourceUpperTraversalCount t j x ω by
      exact_mod_cast hn) (by norm_num))).trans hpoint

/-- The actual annulus upper tail is bounded by crossings and the finite block-success sum. -/
theorem source_upper_annulus_probability_reduction (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ,
      pathLaw (sourceUpperAnnulusHighEvent t s) ≤ pathLaw (sourceUpperCrossingEvent t s) +
        ∑ b ∈ sourceUpperBlockCenters t, pathLaw (sourceUpperBlockSuccess t s b) := by
  filter_upwards [source_upper_annulus_success_reduction hF] with t ht
  intro s
  let U : Set Sample := ⋃ b ∈ sourceUpperBlockCenters t, sourceUpperBlockSuccess t s b
  have hsub : sourceUpperAnnulusHighEvent t s ≤ᵐ[pathLaw]
      (sourceUpperCrossingEvent t s ∪ U : Set Sample) := by
    filter_upwards [ht] with ω hω
    intro hhigh
    rcases hω s hhigh with hc | ⟨b, hb, hs⟩
    · exact Or.inl hc
    · exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hs⟩⟩)
  exact (measure_mono_ae hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (measure_biUnion_finset_le _ _)))

end SRWTightness
