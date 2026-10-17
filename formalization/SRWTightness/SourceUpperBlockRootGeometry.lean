import SRWTightness.SourceUpperBlockRoot
import SRWTightness.SourceUpperBlockCover

open Filter

namespace SRWTightness

/-- Every observed entrance ball after an admissible root excludes the origin. -/
theorem source_upper_root_excludes_origin (t : ℝ) (b : Site) (k j : ℕ)
    (hk : sourceUpperRootAdmissible t b k) (hj : k + 1 ≤ j) :
    (0 : Site) ∉ translateFinset b
      (diskFinset (sourceUpperTraversalRadius t j + sourceUpperBuffer t)) := by
  have hmono := sourceRecordRadius_antitone (sourceUpperRadius t) (Real.exp_pos _).le
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) hj
  change sourceUpperTraversalRadius t j ≤ sourceUpperTraversalRadius t (k + 1) at hmono
  have hr : 0 ≤ sourceUpperTraversalRadius t (k + 1) := by
    unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
    positivity
  have hrj : 0 ≤ sourceUpperTraversalRadius t j := by
    unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
    positivity
  have hH : 0 ≤ sourceUpperBuffer t := by
    unfold sourceUpperBuffer upperTerminalFineRadius
    positivity
  change 2 * sourceUpperTraversalRadius t (k + 1) + sourceUpperBuffer t ≤
    Real.sqrt (normSq b) at hk
  intro hz
  simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq,
    zero_sub, normSq_neg] at hz
  nlinarith [Real.sq_sqrt (normSq_nonneg b)]

/-- Actual selected blocks have the minimal logarithmic root and exclude the origin thereafter. -/
theorem source_upper_block_root_conditions :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      sourceUpperRootAdmissible t b (sourceUpperBlockRoot t b) ∧
      (sourceUpperBlockRoot t b : ℝ) ≤ Real.log t + 1 ∧
      (∀ j < sourceUpperBlockRoot t b, ¬ sourceUpperRootAdmissible t b j) ∧
      ∀ j : ℕ, sourceUpperBlockRoot t b + 1 ≤ j →
        (0 : Site) ∉ translateFinset b
          (diskFinset (sourceUpperTraversalRadius t j + sourceUpperBuffer t)) := by
  filter_upwards [source_upper_block_root_bound, source_upper_block_center_distance]
    with t hr hd
  intro b hb
  obtain ⟨hk, _, hlog⟩ := hr b (hd b hb).1
  have hmin := (source_upper_block_root_spec t b ⟨_, hk⟩).2
  exact ⟨hk, hlog, hmin, fun j hj ↦ source_upper_root_excludes_origin t b _ j hk hj⟩

/-- Exact exponential decay of the source traversal radius from level zero. -/
theorem source_upper_traversal_radius_exp (t : ℝ) (j : ℕ) :
    sourceUpperTraversalRadius t j = sourceUpperTraversalRadius t 0 * Real.exp (-(j : ℝ)) := by
  unfold sourceUpperTraversalRadius sourceRecordRadius
  rw [sub_eq_add_neg, Real.exp_add]
  simp only [Nat.cast_zero, sub_zero]
  ring

/-- Minimality localizes every actual root-level family at the scale R exp(-k). -/
theorem source_upper_root_center_localization :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      b ∈ diskFinset (Real.exp t * Real.exp (-(sourceUpperBlockRoot t b : ℝ))) := by
  filter_upwards [source_upper_block_scale_conditions, source_upper_block_center_distance,
    source_upper_block_root_conditions] with t ht hd hr
  intro b hb
  by_cases hk : sourceUpperBlockRoot t b = 0
  · simpa only [hk, Nat.cast_zero, neg_zero, Real.exp_zero, mul_one] using
      (Finset.mem_filter.mp hb).1
  have ht0 : 0 < t := by linarith [ht.1]
  have hprev := (hr b hb).2.2.1 (sourceUpperBlockRoot t b - 1) (by omega)
  have heq : sourceUpperBlockRoot t b - 1 + 1 = sourceUpperBlockRoot t b := by omega
  have hfail : Real.sqrt (normSq b) <
      2 * sourceUpperTraversalRadius t (sourceUpperBlockRoot t b) + sourceUpperBuffer t := by
    unfold sourceUpperRootAdmissible at hprev
    rw [heq] at hprev
    exact lt_of_not_ge hprev
  have hbR := (div_le_iff₀ (by positivity : 0 < 2 * t)).mp (hd b hb).1
  have hH : sourceUpperBuffer t ≤ Real.sqrt (normSq b) / 2 := by
    apply (mul_le_mul_iff_right₀ ht0).mp
    nlinarith [ht.2.2.1, Real.exp_pos t]
  have hroot := source_upper_traversal_radius_bound t ht.2.1 0
  have hepos := Real.exp_pos (-(sourceUpperBlockRoot t b : ℝ))
  have hrad := mul_le_mul_of_nonneg_right
    (show sourceUpperTraversalRadius t 0 ≤ Real.exp t / 32 by linarith) hepos.le
  rw [← source_upper_traversal_radius_exp] at hrad
  have hnorm : Real.sqrt (normSq b) <
      Real.exp t * Real.exp (-(sourceUpperBlockRoot t b : ℝ)) := by
    nlinarith [mul_pos (Real.exp_pos t) hepos]
  apply (mem_diskFinset _ _).mpr
  change normSq b < _
  nlinarith [Real.sq_sqrt (normSq_nonneg b), Real.sqrt_nonneg (normSq b),
    mul_pos (Real.exp_pos t) hepos]

end SRWTightness
