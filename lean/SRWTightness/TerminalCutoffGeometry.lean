import SRWTightness.GeometricTerminalLogBounds

namespace SRWTightness

theorem terminal_cutoff_le_half (m t a : ℝ) (ht : 2 ≤ t) (ha : 0 ≤ a)
    (hcut : a ≤ m / t ^ 6) : 2 * a ≤ m := by
  have ht0 : 0 < t := by linarith
  have hp : (2 : ℝ) ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) ht 6
  norm_num at hp
  have hm := (le_div_iff₀ (by positivity : 0 < t ^ 6)).mp hcut
  nlinarith

theorem source_terminal_radius_separation (m t A q : ℝ) (ht : 2 ≤ t)
    (hA : 0 < A) (hq : 1 < q) (hcut : A ≤ m / t ^ 6)
    (i : ℕ) (hi : i ≤ geometricTerminalIndex A q (m / t ^ 6) hA hq hcut) :
    2 * (A * q ^ i) ≤ m := by
  have ha := geometric_radius_ge A q hA.le hq.le i
  exact terminal_cutoff_le_half m t _ ht (by linarith)
    ((geometricTerminalIndex_max_iff A q _ hA hq hcut i).mpr hi)

end SRWTightness
