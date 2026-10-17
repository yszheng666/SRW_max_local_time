import SRWTightness.SourceContinuationBandIntegral
import SRWTightness.TerminalRightWindowSum

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- Summing shifted continuation windows cancels the terminal weight normalization. -/
theorem source_continuation_band_scale (t : ℝ) (ν L k : ℕ) (Q : ℝ)
    (P : GeometricGWRecord → ℝ) (hQ : 0 ≤ Q)
    (hd : 4 ≤ sourceLowerTime (sourceLowerRadius t))
    (hP : Integrable P (geometricGWRecordLaw k L)) (hP0 : ∀ r, 0 ≤ P r)
    (hwindow : ∀ q : ℝ,
      q ∈ Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
        (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) →
      (∫ r in sourceContinuationBand t ν L ∩ sourceContinuationWindow t ν L q,
        P r ∂geometricGWRecordLaw k L) ≤ Q * ((1 + q) / sourceLowerTime (sourceLowerRadius t))) :
    (∫ r in sourceContinuationBand t ν L, P r ∂geometricGWRecordLaw k L) ≤ 9 * Q := by
  let d := sourceLowerTime (sourceLowerRadius t)
  let n := ⌊Real.sqrt d⌋₊
  let μ := geometricGWRecordLaw k L
  let B := sourceContinuationBand t ν L
  have hsum : (∑ i ∈ Finset.range (n + 1),
      ∫ r in B ∩ sourceContinuationWindow t ν L (terminalWindowLeft d i), P r ∂μ) ≤
      ∑ i ∈ Finset.range (n + 1), Q * ((1 + terminalWindowLeft d i) / d) := by
    apply Finset.sum_le_sum
    intro i hi
    have hii : i ≤ ⌊Real.sqrt d⌋₊ := by
      have hh := Finset.mem_range.mp hi
      change i < ⌊Real.sqrt d⌋₊ + 1 at hh
      omega
    have hic : (i : ℝ) ≤ (⌊Real.sqrt d⌋₊ : ℝ) := by exact_mod_cast hii
    apply hwindow
    unfold terminalWindowLeft
    exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) i],
      by linarith [Nat.floor_le (Real.sqrt_nonneg d)]⟩
  have hlast := hwindow (2 * Real.sqrt d) ⟨by linarith [Real.sqrt_nonneg d], le_rfl⟩
  have heq : (∑ i ∈ Finset.range (n + 1), Q * ((1 + terminalWindowLeft d i) / d)) +
      Q * ((1 + 2 * Real.sqrt d) / d) = Q * (terminalRightOuterWeight d / d) := by
    unfold terminalRightOuterWeight terminalOuterWindowWeight
    simp only [add_div, mul_add, Finset.sum_div, Finset.mul_sum]
    rfl
  calc
    _ ≤ (∑ i ∈ Finset.range (n + 1),
        ∫ r in B ∩ sourceContinuationWindow t ν L (terminalWindowLeft d i), P r ∂μ) +
        ∫ r in B ∩ sourceContinuationWindow t ν L (2 * Real.sqrt d), P r ∂μ :=
      source_continuation_band_integral_upper t ν L k P hP hP0
    _ ≤ (∑ i ∈ Finset.range (n + 1), Q * ((1 + terminalWindowLeft d i) / d)) +
        Q * ((1 + 2 * Real.sqrt d) / d) := add_le_add hsum hlast
    _ = Q * (terminalRightOuterWeight d / d) := heq
    _ ≤ Q * 9 := mul_le_mul_of_nonneg_left (terminal_right_outer_weight_upper d hd) hQ
    _ = _ := by ring

end SRWTightness
