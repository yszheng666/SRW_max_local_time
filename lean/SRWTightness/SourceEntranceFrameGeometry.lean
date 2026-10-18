import SRWTightness.LatticeNorm
import SRWTightness.DiskFiniteDomain
import Mathlib.Tactic

namespace SRWTightness

/-- Every terminal entrance layer fits a common integer square frame with a fixed radial margin. -/
theorem source_entrance_frame_geometry (m H : ℝ) (hm : 128 ≤ m)
    (hH : 0 ≤ H) (hHm : H ≤ m / 8) :
    ∃ M : ℤ, m ≤ (M : ℝ) ∧ (M : ℝ) ≤ 5 * m / 4 ∧ ∀ z : Site,
      m - H - 1 ≤ Real.sqrt (normSq z) → Real.sqrt (normSq z) ≤ m - H + 1 →
      |z.1| ≤ M ∧ |z.2| ≤ M ∧ (3 * m / 4) ^ 2 ≤ normSq z := by
  let M : ℤ := ⌈m + 1⌉
  have hlo : m + 1 ≤ (M : ℝ) := Int.le_ceil (m + 1)
  have hhi : (M : ℝ) < m + 2 := by
    simpa only [show m + 1 + 1 = m + 2 by ring] using Int.ceil_lt_add_one (m + 1)
  refine ⟨M, by linarith, by linarith, ?_⟩
  intro z hzlo hzhi
  have hs := Real.sq_sqrt (normSq_nonneg z)
  have hn := Real.sqrt_nonneg (normSq z)
  have h1 : |(z.1 : ℝ)| ≤ Real.sqrt (normSq z) := by
    apply (sq_le_sq₀ (abs_nonneg _) hn).mp
    rw [sq_abs]
    dsimp [normSq] at hs ⊢
    nlinarith [sq_nonneg (z.2 : ℝ)]
  have h2 : |(z.2 : ℝ)| ≤ Real.sqrt (normSq z) := by
    apply (sq_le_sq₀ (abs_nonneg _) hn).mp
    rw [sq_abs]
    dsimp [normSq] at hs ⊢
    nlinarith [sq_nonneg (z.1 : ℝ)]
  have h1M : |(z.1 : ℝ)| ≤ (M : ℝ) := by linarith
  have h2M : |(z.2 : ℝ)| ≤ (M : ℝ) := by linarith
  refine ⟨by exact_mod_cast h1M, by exact_mod_cast h2M, ?_⟩
  have hr : 3 * m / 4 ≤ Real.sqrt (normSq z) := by linarith
  have hb := (sq_le_sq₀ (by linarith : 0 ≤ 3 * m / 4) hn).mpr hr
  nlinarith

end SRWTightness
