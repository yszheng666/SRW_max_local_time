import SRWTightness.SourceUpperInteriorWitness
import SRWTightness.SourceUpperDisplacedTraversalComparison
import SRWTightness.SourceUpperBoundarySource

open Filter MeasureTheory
open scoped Classical

namespace SRWTightness

/-- Closed high points reduce to the original open crossing event and block success. -/
theorem source_upper_closed_success_reduction (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      ω ∈ sourceUpperClosedCutoffEvent t s →
        ω ∈ sourceUpperNearOriginHighEvent t s ∨ ω ∈ sourceUpperCrossingEvent t s ∨
          ∃ b ∈ sourceUpperBlockCenters t, ω ∈ sourceUpperBlockSuccess t s b := by
  filter_upwards [source_upper_block_count_le_displaced_point_ae hF, source_upper_block_cover,
    source_upper_block_side_ge_four] with t hc hcover hside
  have hh := ae_all_iff.mpr (fun b : sourceUpperBlockCenters t ↦ hc b b.property)
  filter_upwards [hh] with ω hω
  intro s hs
  obtain ⟨x, hxhi, hhigh⟩ := hs
  by_cases hnear : Real.sqrt (normSq x) ≤ Real.exp t / t
  · left
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, hnear⟩, hhigh⟩
    apply (mem_diskFinset _ _).mpr
    have hsq : normSq x ≤ (Real.exp t / 2) ^ 2 := by
      calc
        _ = Real.sqrt (normSq x) ^ 2 := (Real.sq_sqrt (normSq_nonneg x)).symm
        _ ≤ _ := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hxhi
    exact hsq.trans_lt (by nlinarith [sq_pos_of_pos (Real.exp_pos t)])
  right
  by_cases hcross : ω ∈ sourceUpperCrossingEvent t s
  · exact Or.inl hcross
  right
  obtain ⟨b, hb, hxb⟩ := hcover x (lt_of_not_ge hnear) hxhi
  obtain ⟨y, hy, hdist⟩ := source_upper_block_interior_witness t b x hside hxb hxhi
  refine ⟨b, hb, ⟨⟨⟨x, hxb⟩, hhigh⟩, ?_⟩⟩
  intro j hj hJ
  have hpoint : Real.sqrt (2 * (sourceUpperTraversalCount t j y ω : ℝ)) ≤
      sourceUpperBarrier t s j := by
    apply le_of_not_gt
    intro hgt
    apply hcross
    simp only [sourceUpperCrossingEvent, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨y, hy, j, Finset.mem_range.mpr (by omega), hgt⟩
  have hn := hω ⟨b, hb⟩ j hj.le hJ y hdist
  exact (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (show (sourceUpperBlockCount t b j ω : ℝ) ≤ sourceUpperTraversalCount t j y ω by
      exact_mod_cast hn) (by norm_num))).trans hpoint


/-- The closed half-disk indicator needs only the original three contributions. -/
theorem source_upper_closed_forest_indicator (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      (if ω ∈ sourceUpperClosedCutoffEvent t s then (1 : ℝ) else 0) ≤
        (if ω ∈ sourceUpperNearOriginHighEvent t s then (1 : ℝ) else 0) +
        (if ω ∈ sourceUpperCrossingEvent t s then (1 : ℝ) else 0) +
        ∑ b ∈ sourceUpperBlockCenters t,
          (if ω ∈ sourceUpperBlockSuccess t s b then (1 : ℝ) else 0) := by
  classical
  filter_upwards [source_upper_closed_success_reduction hF] with t ht
  filter_upwards [ht] with ω hω
  intro s
  have hsum : 0 ≤ ∑ b ∈ sourceUpperBlockCenters t,
      (if ω ∈ sourceUpperBlockSuccess t s b then (1 : ℝ) else 0) :=
    Finset.sum_nonneg (fun _ _ ↦ by positivity)
  by_cases hi : ω ∈ sourceUpperClosedCutoffEvent t s
  · rcases hω s hi with hn | hc | ⟨b, hb, hsucc⟩
    · simp only [if_pos hi, if_pos hn]
      split_ifs <;> linarith
    · simp only [if_pos hi, if_pos hc]
      split_ifs <;> linarith
    · have hh := Finset.single_le_sum
        (fun a (_ : a ∈ sourceUpperBlockCenters t) ↦
          show 0 ≤ (if ω ∈ sourceUpperBlockSuccess t s a then (1 : ℝ) else 0) by positivity) hb
      simp only [if_pos hsucc] at hh
      simp only [if_pos hi]
      split_ifs <;> linarith
  · simp only [if_neg hi]
    split_ifs <;> linarith


/-- The three-term closed indicator with actual direct buffered traversals. -/
theorem source_upper_closed_direct_indicator (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      (if ω ∈ sourceUpperClosedCutoffEvent t s then (1 : ℝ) else 0) ≤
        (if ω ∈ sourceUpperNearOriginHighEvent t s then (1 : ℝ) else 0) +
        (if ω ∈ sourceUpperCrossingEvent t s then (1 : ℝ) else 0) +
        ∑ b ∈ sourceUpperBlockCenters t,
          (if ω ∈ sourceUpperDirectBlockSuccess t s b then (1 : ℝ) else 0) := by
  filter_upwards [source_upper_closed_forest_indicator hF,
    source_upper_direct_block_success_iff_ae hF] with t hi he
  filter_upwards [hi, he] with ω hi he
  intro s
  have hsum : (∑ b ∈ sourceUpperBlockCenters t,
      (if ω ∈ sourceUpperDirectBlockSuccess t s b then (1 : ℝ) else 0)) =
      ∑ b ∈ sourceUpperBlockCenters t,
        (if ω ∈ sourceUpperBlockSuccess t s b then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro b hb
    simp only [he b hb s]
  rw [hsum]
  exact hi s


end SRWTightness
