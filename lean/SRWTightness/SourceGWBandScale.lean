import SRWTightness.SourceGWBandIntegral
import SRWTightness.TerminalRightWindowSum

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- Summing normalized marked-window bounds gives the full reference success scale. -/
theorem source_gw_band_integral_scale (t : ℝ) (L : ℕ) (c C : ℝ)
    (P : GeometricGWRecord → ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hd : 4 ≤ sourceLowerTime (sourceLowerRadius t))
    (hP : Integrable P (geometricGWRecordLaw 1 L)) (hP0 : ∀ r, 0 ≤ P r)
    (hwindow : ∀ q : ℝ,
      q ∈ Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
        (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) →
      let d := sourceLowerTime (sourceLowerRadius t)
      let E := sourceGWCoarseWindowEvent t L q
      let B := sourceGWCoarseBandEvent t L
      (E ⊆ B → c * (Real.exp (-2 * t) * (1 + q) / d) ≤
        ∫ r in E, P r ∂geometricGWRecordLaw 1 L) ∧
      (∫ r in B ∩ E, P r ∂geometricGWRecordLaw 1 L) ≤
        C * (Real.exp (-2 * t) * (1 + q) / d)) :
    (c / 2) * Real.exp (-2 * t) ≤
        (∫ r in sourceGWCoarseBandEvent t L, P r ∂geometricGWRecordLaw 1 L) ∧
      (∫ r in sourceGWCoarseBandEvent t L, P r ∂geometricGWRecordLaw 1 L) ≤
        (9 * C) * Real.exp (-2 * t) := by
  let d := sourceLowerTime (sourceLowerRadius t)
  let n := ⌊Real.sqrt d⌋₊
  let μ := geometricGWRecordLaw 1 L
  let B := sourceGWCoarseBandEvent t L
  have hsumL : (∑ i ∈ Finset.range n,
      c * (Real.exp (-2 * t) * (1 + (terminalWindowLeft d i + 1)) / d)) ≤
      ∑ i ∈ Finset.range n,
        ∫ r in sourceGWCoarseWindowEvent t L (terminalWindowLeft d i + 1), P r ∂μ := by
    apply Finset.sum_le_sum
    intro i hi
    have hii : i < ⌊Real.sqrt d⌋₊ := Finset.mem_range.mp hi
    exact (hwindow _ (terminal_right_inner_window d i hii).1).1
      (source_gw_inner_window_subset t L i hii)
  have heqL : (∑ i ∈ Finset.range n,
      c * (Real.exp (-2 * t) * (1 + (terminalWindowLeft d i + 1)) / d)) =
      c * Real.exp (-2 * t) * (terminalRightInnerWeight d / d) := by
    simp only [terminalRightInnerWeight, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsumU : (∑ i ∈ Finset.range (n + 1),
      ∫ r in B ∩ sourceGWCoarseWindowEvent t L (terminalWindowLeft d i), P r ∂μ) ≤
      ∑ i ∈ Finset.range (n + 1), C * (Real.exp (-2 * t) * (1 + terminalWindowLeft d i) / d) := by
    apply Finset.sum_le_sum
    intro i hi
    have hii : i ≤ ⌊Real.sqrt d⌋₊ := by
      have hh := Finset.mem_range.mp hi
      change i < ⌊Real.sqrt d⌋₊ + 1 at hh
      omega
    have hic : (i : ℝ) ≤ (⌊Real.sqrt d⌋₊ : ℝ) := by exact_mod_cast hii
    have hq : terminalWindowLeft d i ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) := by
      unfold terminalWindowLeft
      exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) i],
        by linarith [Nat.floor_le (Real.sqrt_nonneg d)]⟩
    exact (hwindow _ hq).2
  have hlast : (∫ r in B ∩ sourceGWCoarseWindowEvent t L (2 * Real.sqrt d), P r ∂μ) ≤
      C * (Real.exp (-2 * t) * (1 + 2 * Real.sqrt d) / d) :=
    (hwindow _ ⟨by linarith [Real.sqrt_nonneg d], le_rfl⟩).2
  have heqU : (∑ i ∈ Finset.range (n + 1),
      C * (Real.exp (-2 * t) * (1 + terminalWindowLeft d i) / d)) +
      C * (Real.exp (-2 * t) * (1 + 2 * Real.sqrt d) / d) =
      C * Real.exp (-2 * t) * (terminalRightOuterWeight d / d) := by
    have heq : (∑ i ∈ Finset.range (n + 1),
        C * (Real.exp (-2 * t) * (1 + terminalWindowLeft d i) / d)) =
        C * Real.exp (-2 * t) * (terminalOuterWindowWeight d / d) := by
      simp only [terminalOuterWindowWeight, Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq]
    unfold terminalRightOuterWeight
    ring
  constructor
  · calc
      _ = c * Real.exp (-2 * t) * (1 / 2) := by ring
      _ ≤ c * Real.exp (-2 * t) * (terminalRightInnerWeight d / d) :=
        mul_le_mul_of_nonneg_left (terminal_right_inner_weight_lower d hd) (by positivity)
      _ = _ := heqL.symm
      _ ≤ _ := hsumL
      _ ≤ _ := source_gw_band_integral_lower t L P hP hP0
  · calc
      _ ≤ _ := source_gw_band_integral_upper t L P hP hP0
      _ ≤ _ := add_le_add hsumU hlast
      _ = C * Real.exp (-2 * t) * (terminalRightOuterWeight d / d) := heqU
      _ ≤ C * Real.exp (-2 * t) * 9 :=
        mul_le_mul_of_nonneg_left (terminal_right_outer_weight_upper d hd) (by positivity)
      _ = _ := by ring

end SRWTightness
