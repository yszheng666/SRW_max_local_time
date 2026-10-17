import SRWTightness.ExternalGWBarrier
import Mathlib.Tactic.Linarith

namespace SRWTightness

/-- Rounding half the squared lower endpoint produces a positive population in a short interval. -/
theorem gw_positive_lattice_interval (a δ : ℝ) (ha : 0 < a) (hδ : 0 ≤ δ)
    (hwidth : 2 ≤ 2 * a * δ + δ ^ 2) : gwPositiveLatticeIntersects a (a + δ) := by
  let n : ℕ := ⌈a ^ 2 / 2⌉₊
  have hnlo : a ^ 2 / 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) < a ^ 2 / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnpos : 0 < n := by
    by_contra hh
    have hnzero : n = 0 := by omega
    simp only [hnzero, Nat.cast_zero] at hnlo
    nlinarith
  have hn0 : 0 ≤ 2 * (n : ℝ) := by positivity
  have hs0 := Real.sqrt_nonneg (2 * (n : ℝ))
  have hs := Real.sq_sqrt hn0
  refine ⟨n, hnpos, ?_, ?_⟩ <;> nlinarith

/-- A width-two interval with upper endpoint at least four contains a positive state. -/
theorem gw_positive_lattice_wide_interval (a b : ℝ) (hb : 4 ≤ b) (hab : a + 2 ≤ b) :
    gwPositiveLatticeIntersects a b := by
  have hm : 2 ≤ max a 2 := le_max_right _ _
  obtain ⟨n, hn, hl, hu⟩ := gw_positive_lattice_interval (max a 2) 1
    (by linarith) (by norm_num) (by nlinarith)
  refine ⟨n, hn, (le_max_left _ _).trans hl, ?_⟩
  have hmax : max a 2 ≤ b - 1 := max_le (by linarith) (by linarith)
  linarith

/-- The source's closed half-unit subwindow contains a positive terminal population. -/
theorem gw_terminal_subwindow_lattice (u : ℝ) (hu : 2 ≤ u) :
    gwPositiveLatticeIntersects (u + 1 / 4) (u + 3 / 4) := by
  have hh := gw_positive_lattice_interval (u + 1 / 4) (1 / 2)
    (by linarith) (by norm_num) (by nlinarith)
  convert hh using 1 <;> ring

/-- The closed subwindow stays strictly inside the half-open terminal window. -/
theorem gw_terminal_subwindow_subset (u : ℝ) :
    Set.Icc (u + 1 / 4) (u + 3 / 4) ⊆ Set.Ico u (u + 1) := by
  intro z hz
  exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

end SRWTightness
