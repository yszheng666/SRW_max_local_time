import SRWTightness.SourceUpperMeshScale
import SRWTightness.SourceUpperFineRatioLimit

open Filter
open scoped Topology

namespace SRWTightness

/-- The exact integer side length r=floor(exp(D_+/4)) used by the source upper blocks. -/
noncomputable def sourceUpperBlockSide (t : ℝ) : ℕ :=
  ⌊Real.exp (sourceUpperLogRadius t / 4)⌋₊

theorem sourceUpperBlockSide_cast (t : ℝ) :
    (sourceUpperBlockSide t : ℝ) = upperTerminalFineRadius (sourceUpperLogRadius t) := rfl

/-- The actual block side is positive even before the eventual source regime. -/
theorem sourceUpperBlockSide_pos (t : ℝ) : 0 < sourceUpperBlockSide t := by
  have h : 1 ≤ sourceUpperBlockSide t :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr (by
      unfold sourceUpperLogRadius
      positivity))
  omega

/-- The source block buffer is negligible compared with the inner annulus radius R/t. -/
theorem source_upper_block_scale_conditions :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ 32 * sourceUpperRadius t ≤ Real.exp t ∧
      t * sourceUpperBuffer t ≤ Real.exp t / 8 ∧
      (sourceUpperBlockSide t : ℝ) ≤ Real.exp t / 4 := by
  have hsmall := source_upper_fine_ratio_limit.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [source_upper_mesh_scale_conditions, hsmall,
    eventually_ge_atTop (1 : ℝ)] with t ht hs ht1
  have ht0 : 0 < t := by linarith
  have hr : 1 ≤ upperTerminalFineRadius (sourceUpperLogRadius t) := by
    have h : 1 ≤ sourceUpperBlockSide t := sourceUpperBlockSide_pos t
    rw [← sourceUpperBlockSide_cast]
    exact_mod_cast h
  have hratio := (div_lt_iff₀ (Real.exp_pos (sourceUpperLogRadius t))).mp hs
  change t * upperTerminalFineRadius (sourceUpperLogRadius t) <
    1 / 4 * sourceUpperRadius t at hratio
  have hbuf : t * sourceUpperBuffer t ≤ Real.exp t / 8 := by
    unfold sourceUpperBuffer
    nlinarith [mul_le_mul_of_nonneg_left hr ht0.le, ht.1]
  have hB : 0 ≤ sourceUpperBuffer t := by unfold sourceUpperBuffer; positivity
  have hrB : (sourceUpperBlockSide t : ℝ) ≤ sourceUpperBuffer t := by
    rw [sourceUpperBlockSide_cast]
    unfold sourceUpperBuffer
    linarith
  have hside : (sourceUpperBlockSide t : ℝ) ≤ Real.exp t / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hB, Real.exp_pos t]
  exact ⟨ht1, ht.1, hbuf, hside⟩

end SRWTightness
