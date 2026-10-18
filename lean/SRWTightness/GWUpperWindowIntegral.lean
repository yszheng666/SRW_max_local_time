import SRWTightness.GeometricGWLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.Order.Floor.Ring

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Unit terminal windows above t-1 cover all heights at most3t with a finite index set. -/
theorem gw_upper_window_cover (t u : ℝ) (hlo : t - 1 ≤ u) (hhi : u ≤ 3 * t) :
    ∃ i ∈ Finset.range (⌊2 * t + 1⌋₊ + 1),
      u ∈ Set.Ico (t - 1 + i) (t - 1 + i + 1) := by
  let i := ⌊u - (t - 1)⌋₊
  have hl := Nat.floor_le (show 0 ≤ u - (t - 1) by linarith)
  have hu := Nat.lt_floor_add_one (u - (t - 1))
  have hi : i ≤ ⌊2 * t + 1⌋₊ := Nat.floor_mono (by linarith)
  refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
  change t - 1 + (i : ℝ) ≤ u ∧ u < t - 1 + (i : ℝ) + 1
  dsimp [i]
  constructor <;> linarith

/-- Windowwise terminal majorants bound a band integral by weighted window probabilities. -/
theorem gw_upper_window_integral (t : ℝ) (J n : ℕ) (B : Set GeometricGWRecord)
    (F : ℝ → ℝ≥0∞) (w : ℕ → ℝ≥0∞)
    (hB : ∀ g ∈ B, geometricGWHeight g n ≤ 3 * t)
    (hw : ∀ i ∈ Finset.range (⌊2 * t + 1⌋₊ + 1),
      ∀ u ∈ Set.Ico (t - 1 + i) (t - 1 + i + 1), F u ≤ w i) :
    (∫⁻ g in B, if t - 1 ≤ geometricGWHeight g n then F (geometricGWHeight g n) else 0
      ∂geometricGWRecordLaw J n) ≤
      ∑ i ∈ Finset.range (⌊2 * t + 1⌋₊ + 1), w i * geometricGWRecordLaw J n
        {g | g ∈ B ∧ geometricGWHeight g n ∈ Set.Ico (t - 1 + i) (t - 1 + i + 1)} := by
  classical
  let I := Finset.range (⌊2 * t + 1⌋₊ + 1)
  let S := fun i : ℕ ↦ {g : GeometricGWRecord |
    g ∈ B ∧ geometricGWHeight g n ∈ Set.Ico (t - 1 + i) (t - 1 + i + 1)}
  have hpoint (g : GeometricGWRecord) :
      B.indicator (fun g ↦ if t - 1 ≤ geometricGWHeight g n then
        F (geometricGWHeight g n) else 0) g ≤
          ∑ i ∈ I, (S i).indicator (fun _ ↦ w i) g := by
    by_cases hg : g ∈ B
    · rw [Set.indicator_of_mem hg]
      by_cases hlo : t - 1 ≤ geometricGWHeight g n
      · rw [if_pos hlo]
        obtain ⟨i, hi, hwin⟩ := gw_upper_window_cover t _ hlo (hB g hg)
        have his : g ∈ S i := ⟨hg, hwin⟩
        have hsum := Finset.single_le_sum (fun j (_ : j ∈ I) ↦
          show 0 ≤ (S j).indicator (fun _ ↦ w j) g from bot_le) (show i ∈ I from hi)
        rw [Set.indicator_of_mem his] at hsum
        exact (hw i hi _ hwin).trans hsum
      · rw [if_neg hlo]
        exact bot_le
    · rw [Set.indicator_of_notMem hg]
      exact bot_le
  rw [← lintegral_indicator (Set.to_countable B).measurableSet]
  apply (lintegral_mono hpoint).trans_eq
  rw [lintegral_finsetSum I (fun _ _ ↦ measurable_of_countable _)]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator_const (Set.to_countable (S i)).measurableSet (w i)

end SRWTightness
