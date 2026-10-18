import SRWTightness.SourceUpperDirectBlockSuccess
import SRWTightness.SourceUpperInnerReduction

open Filter MeasureTheory
open scoped Classical

namespace SRWTightness

/-- Direct buffered counts and forest counts identify all block-success events on one almost-sure set. -/
theorem source_upper_direct_block_success_iff_ae (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ b ∈ sourceUpperBlockCenters t, ∀ s : ℝ,
      ω ∈ sourceUpperDirectBlockSuccess t s b ↔ ω ∈ sourceUpperBlockSuccess t s b := by
  filter_upwards [source_upper_block_count_eq_direct_ae hF] with t ht
  have hh := ae_all_iff.mpr (fun b : sourceUpperBlockCenters t ↦ ht b b.property)
  filter_upwards [hh] with ω hω
  intro b hb s
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro _
  constructor
  · intro h j hj hJ
    rw [hω ⟨b, hb⟩ j hj.le hJ]
    exact h j hj hJ
  · intro h j hj hJ
    rw [← hω ⟨b, hb⟩ j hj.le hJ]
    exact h j hj hJ

/-- The open half-radius indicator inequality with actual directly extracted block traversals. -/
theorem source_upper_open_direct_indicator (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ᵐ ω ∂pathLaw, ∀ s : ℝ,
      (if ω ∈ sourceUpperInnerHighEvent t s then (1 : ℝ) else 0) ≤
        (if ω ∈ sourceUpperNearOriginHighEvent t s then (1 : ℝ) else 0) +
        (if ω ∈ sourceUpperCrossingEvent t s then (1 : ℝ) else 0) +
        ∑ b ∈ sourceUpperBlockCenters t,
          (if ω ∈ sourceUpperDirectBlockSuccess t s b then (1 : ℝ) else 0) := by
  filter_upwards [source_upper_inner_indicator_reduction hF,
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
