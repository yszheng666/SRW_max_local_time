import SRWTightness.SourceUpperBlockScales
import SRWTightness.SourceUpperDepthEventually

open Filter
namespace SRWTightness

/-- Literal source (4.1), retaining the integer side, signed floor and actual Green depth. -/
theorem source_upper_scale_parameters (R : ℝ) (hR : 0 < R)
    (hlog : 1 ≤ Real.log (R / (32 * sourceUpperRadius (Real.log R)))) :
    sourceUpperLogRadius (Real.log R) = (8 * Real.log (Real.log R)) ^ 4 ∧
    sourceUpperRadius (Real.log R) = Real.exp (sourceUpperLogRadius (Real.log R)) ∧
    sourceUpperBlockSide (Real.log R) =
      Nat.floor (sourceUpperRadius (Real.log R) ^ (1 / 4 : ℝ)) ∧
    sourceUpperBuffer (Real.log R) = 4 * (sourceUpperBlockSide (Real.log R) : ℝ) + 10 ∧
    (sourceRootDepth R (sourceUpperRadius (Real.log R)) : ℤ) =
      Int.floor (Real.log (R / (32 * sourceUpperRadius (Real.log R)))) ∧
    (sourceUpperCoarseDepth (Real.log R) : ℤ) =
      Int.floor (Real.log (R / (32 * sourceUpperRadius (Real.log R)))) - 1 ∧
    upperTerminalDepth (sourceUpperLogRadius (Real.log R)) =
      diskGreen (Real.exp 1 * sourceUpperRadius (Real.log R) - 1) 0 0 / (2 / Real.pi) ∧
    sourceUpperTotalDepth (Real.log R) = (sourceUpperCoarseDepth (Real.log R) : ℝ) +
      upperTerminalDepth (sourceUpperLogRadius (Real.log R)) ∧
    Real.log (upperTerminalFineRadius (sourceUpperLogRadius (Real.log R))) =
      Real.log (sourceUpperBlockSide (Real.log R) : ℝ) := by
  have hf : (sourceRootDepth R (sourceUpperRadius (Real.log R)) : ℤ) =
      Int.floor (Real.log (R / (32 * sourceUpperRadius (Real.log R)))) :=
    Int.natCast_floor_eq_floor (by linarith)
  have hn : 1 ≤ sourceRootDepth R (sourceUpperRadius (Real.log R)) :=
    (Nat.one_le_floor_iff _).mpr hlog
  refine ⟨rfl, rfl, ?_, rfl, hf, ?_, ?_, rfl, rfl⟩
  · have he : sourceUpperRadius (Real.log R) ^ (1 / 4 : ℝ) =
        Real.exp (sourceUpperLogRadius (Real.log R) / 4) := by
      rw [sourceUpperRadius, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [he]
    rfl
  · unfold sourceUpperCoarseDepth
    rw [Real.exp_log hR, Nat.cast_sub hn, Nat.cast_one, hf]
  · unfold upperTerminalDepth upperTerminalRadius sourceUpperRadius
    rw [Real.exp_add]
    congr 3
    ring

/-- The literal source root logarithm is at least one eventually in the original radius. -/
theorem source_upper_scale_parameter_range :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      1 ≤ Real.log (R / (32 * sourceUpperRadius (Real.log R))) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually source_upper_coarse_range_eventually] with R hR ht
  have he := source_upper_root_log (Real.log R)
  rw [Real.exp_log hR] at he
  exact ⟨hR, by rw [he]; exact ht⟩

end SRWTightness
