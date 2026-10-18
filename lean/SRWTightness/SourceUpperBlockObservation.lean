import SRWTightness.SourceUpperBlockCover

open Filter

namespace SRWTightness

/-- The actual centered half-open block fits in a strict ball of twice its side length. -/
theorem sourceUpperBlock_subset_observation_ball (t : ℝ) (b : Site) :
    sourceUpperBlock t b ⊆ translateFinset b
      (diskFinset (2 * upperTerminalFineRadius (sourceUpperLogRadius t))) := by
  intro x hx
  apply (mem_translateFinset_iff b _ x).mpr
  apply (mem_diskFinset _ _).mpr
  have h := centeredLatticeBlock_near (sourceUpperBlockSide t) b x hx
  rw [sourceUpperBlockSide_cast] at h
  have hr : (0 : ℝ) < upperTerminalFineRadius (sourceUpperLogRadius t) := by
    change (0 : ℝ) < (sourceUpperBlockSide t : ℝ)
    exact_mod_cast sourceUpperBlockSide_pos t
  change normSq (x - b) < _
  nlinarith

/-- Actual upper blocks lie inside the innermost observation region for the visit decomposition. -/
theorem source_upper_block_observation_conditions :
    ∀ᶠ t : ℝ in atTop,
      sourceUpperBuffer t + 2 ≤ sourceUpperRadius t ∧
      ∀ b : Site, sourceUpperBlock t b ⊆ translateFinset b
        (diskFinset (sourceUpperRadius t - sourceUpperBuffer t - 2)) := by
  filter_upwards [eventually_ge_atTop (max 10 (Real.exp 1))] with t ht
  have ht10 : 10 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hl : 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans ht)
    simpa only [Real.log_exp] using h
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  have hr : 1 ≤ r := by
    change (1 : ℝ) ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  have hf := source_upper_fine_ratio_bound t ht0 hl
  have hquad := (div_le_div_iff₀ (Real.exp_pos (sourceUpperLogRadius t)) ht0).mp hf
  have hmul := mul_le_mul_of_nonneg_right (show 100 ≤ t ^ 2 by nlinarith)
    (show 0 ≤ r by linarith)
  have hbig : 100 * r ≤ sourceUpperRadius t := by
    change t * r * t ≤ 1 * sourceUpperRadius t at hquad
    nlinarith only [hquad, hmul]
  have hH : sourceUpperBuffer t = 4 * r + 10 := rfl
  have hsep : 2 * r ≤ sourceUpperRadius t - sourceUpperBuffer t - 2 := by
    rw [hH]
    linarith
  refine ⟨by linarith, ?_⟩
  intro b
  exact (sourceUpperBlock_subset_observation_ball t b).trans
    (Finset.image_subset_image (diskFinset_mono _ _ (by positivity) hsep))

end SRWTightness
