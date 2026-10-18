import SRWTightness.CommonGapTerminalError
import SRWTightness.SourceEarlyGapWeight

namespace SRWTightness

/-- A fixed distance-index threshold makes the actual early terminal error small. -/
theorem source_early_terminal_error_small (W t ρ : ℝ) (a J₀ : ℕ)
    (hW : 0 ≤ W) (hρ : 1 ≤ ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (ha : a = sourceCommonPairDistanceIndex t ρ)
    (hJ : sourceEarlyDistanceGap a J₀ ≤ a)
    (hsep : 2 * ρ ≤ sourceCommonPairInnerRadius t (a - sourceEarlyDistanceGap a J₀))
    (hlarge : 6 * Real.exp 1 * W ≤ ((a : ℝ) + 1) ^ 2) :
    W * (2 * ρ + 1) / sourceCommonPairInnerRadius t (a - sourceEarlyDistanceGap a J₀) *
      Real.log (sourceCommonPairInnerRadius t (a - sourceEarlyDistanceGap a J₀) /
        (2 * ρ)) ≤ 1 / 2 := by
  let J := sourceEarlyDistanceGap a J₀
  have hb := source_common_gap_terminal_error W t ρ (a - J) J hW hρ houter
    ((Nat.sub_add_cancel hJ).trans ha) hsep
  have hw := source_early_gap_weight a J₀ hJ
  have hn : 0 ≤ ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) := by positivity
  have hh := mul_le_mul_of_nonneg_right hlarge hn
  have hbound : 3 * Real.exp 1 * W * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) ≤
      1 / 2 := by
    change ((a : ℝ) + 1) ^ 2 * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) ≤ 1 at hw
    nlinarith only [hh, hw]
  exact hb.trans hbound

end SRWTightness
