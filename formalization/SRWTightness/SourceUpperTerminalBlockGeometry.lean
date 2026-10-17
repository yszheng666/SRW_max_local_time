import SRWTightness.SourceUpperBlockObservation
import SRWTightness.SourceUpperMarkRadius

open Filter

namespace SRWTightness

/-- Centered half-open blocks translate exactly with their distinguished center. -/
theorem sourceUpperBlock_translate (t : ℝ) (b : Site) :
    translateFinset b (sourceUpperBlock t 0) = sourceUpperBlock t b := by
  ext x
  simp only [mem_translateFinset_iff, sourceUpperBlock, centeredLatticeBlock, latticeSquare,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
  change ((_ ≤ x.1 - b.1 ∧ x.1 - b.1 ≤ _) ∧
    (_ ≤ x.2 - b.2 ∧ x.2 - b.2 ≤ _)) ↔ _
  simp only [Prod.fst_zero, Prod.snd_zero]
  omega

/-- The actual centered upper block is nonempty. -/
theorem sourceUpperBlock_nonempty (t : ℝ) : (sourceUpperBlock t 0).Nonempty := by
  refine ⟨0, ?_⟩
  have ha := sourceUpperBlockSide_pos t
  simp only [sourceUpperBlock, centeredLatticeBlock, latticeSquare,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero]
  have hh : sourceUpperBlockSide t / 2 < sourceUpperBlockSide t := Nat.div_lt_self ha (by norm_num)
  constructor <;> constructor <;> omega

/-- Actual upper blocks satisfy the terminal bound’s geometry conditions. -/
theorem source_upper_terminal_block_geometry :
    ∀ᶠ t : ℝ in atTop,
      (∀ x ∈ sourceUpperBlock t 0,
        normSq x ≤ ((1 - (1 / 2 : ℝ)) * sourceUpperMarkRadius t) ^ 2) ∧
      (∀ x ∈ sourceUpperBlock t 0, ∀ y ∈ sourceUpperBlock t 0,
        normSq (x - y) ≤ (2 * upperTerminalFineRadius (sourceUpperLogRadius t)) ^ 2) ∧
      sourceUpperBlock t 0 ⊆ diskFinset (sourceUpperMarkRadius t) ∧
      sourceUpperBlock t 0 ⊆ diskFinset (2 * upperTerminalFineRadius (sourceUpperLogRadius t)) := by
  filter_upwards [source_upper_block_observation_conditions] with t ht
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  have hr : 0 ≤ r := by unfold r upperTerminalFineRadius; positivity
  have hH : sourceUpperBuffer t = 4 * r + 10 := rfl
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  have hR : 2 * r < sourceUpperMarkRadius t := by
    unfold sourceUpperMarkRadius
    have := mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le hm.le
    rw [hH]
    linarith [ht.1]
  have hn (x : Site) (hx : x ∈ sourceUpperBlock t 0) : normSq x ≤ r ^ 2 := by
    have hh := centeredLatticeBlock_near (sourceUpperBlockSide t) 0 x hx
    simpa only [sub_zero, sourceUpperBlockSide_cast] using hh
  have hobs : sourceUpperBlock t 0 ⊆ diskFinset (2 * r) := by
    simpa only [translateFinset, zero_add, Finset.image_id'] using
      sourceUpperBlock_subset_observation_ball t 0
  refine ⟨?_, ?_, ?_, hobs⟩
  · intro x hx
    have hh := hn x hx
    change normSq x ≤ ((1 - (1 / 2 : ℝ)) * sourceUpperMarkRadius t) ^ 2
    nlinarith [normSq_nonneg x]
  · intro x hx y hy
    have hh := normSq_add_bound x (-y) hr hr (hn x hx) (by simpa only [normSq_neg] using hn y hy)
    simpa only [sub_eq_add_neg, show r + r = 2 * r by ring] using hh
  · exact hobs.trans (diskFinset_mono _ _ (by positivity) hR.le)

end SRWTightness
