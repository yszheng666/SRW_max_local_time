import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace SRWTightness

/-- The unit tent of height one half, supported on the unit interval. -/
noncomputable def schauderTent (t : ℝ) : ℝ := max 0 (min t (1 - t))

theorem schauderTent_continuous : Continuous schauderTent := by
  unfold schauderTent
  fun_prop

theorem schauderTent_nonneg (t : ℝ) : 0 ≤ schauderTent t := le_max_left _ _

theorem schauderTent_le_half (t : ℝ) : schauderTent t ≤ 1 / 2 := by
  apply max_le (by norm_num)
  by_cases h : t ≤ 1 / 2
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem schauderTent_eq_zero_left (t : ℝ) (ht : t ≤ 0) : schauderTent t = 0 := by
  exact max_eq_left ((min_le_left _ _).trans ht)

theorem schauderTent_eq_zero_right (t : ℝ) (ht : 1 ≤ t) : schauderTent t = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem schauderTent_pos_iff (t : ℝ) : 0 < schauderTent t ↔ 0 < t ∧ t < 1 := by
  simp only [schauderTent, lt_max_iff, lt_self_iff_false, false_or, lt_min_iff]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- A translated and dilated tent; its amplitude is supplied separately. -/
noncomputable def scaledSchauderTent (a b c t : ℝ) : ℝ := c * schauderTent (a * t - b)

theorem scaledSchauderTent_continuous (a b c : ℝ) :
    Continuous (scaledSchauderTent a b c) := by
  exact continuous_const.mul (schauderTent_continuous.comp
    ((continuous_const.mul continuous_id).sub continuous_const))

theorem scaledSchauderTent_bounds (a b c t : ℝ) (hc : 0 ≤ c) :
    0 ≤ scaledSchauderTent a b c t ∧ scaledSchauderTent a b c t ≤ c / 2 := by
  constructor
  · exact mul_nonneg hc (schauderTent_nonneg _)
  · have h := mul_le_mul_of_nonneg_left (schauderTent_le_half (a * t - b)) hc
    simpa [scaledSchauderTent, div_eq_mul_inv] using h

/-- Integer translates have disjoint positive supports. -/
theorem schauderTent_translate_disjoint (x : ℝ) (k l : ℕ) (hkl : k ≠ l)
    (hk : 0 < schauderTent (x - k)) : schauderTent (x - l) = 0 := by
  obtain ⟨hk0, hk1⟩ := (schauderTent_pos_iff _).mp hk
  rcases lt_or_gt_of_ne hkl with h | h
  · have hn : (k : ℝ) + 1 ≤ l := by exact_mod_cast Nat.succ_le_of_lt h
    apply schauderTent_eq_zero_left
    linarith
  · have hn : (l : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt h
    apply schauderTent_eq_zero_right
    linarith

end SRWTightness
