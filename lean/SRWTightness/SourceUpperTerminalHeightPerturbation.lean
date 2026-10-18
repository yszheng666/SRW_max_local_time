import SRWTightness.SourceUpperGaussianShift

namespace SRWTightness

/-- A bounded downward threshold error preserves the full linear and quadratic tail envelope. -/
theorem source_upper_terminal_height_perturbation (q ε E κ d : ℝ)
    (hE : 0 ≤ E) (hκ : 0 < κ) (hd : 1 ≤ d) (hε : -E ≤ ε) :
    Real.exp (-2 * (q + ε) - κ * (max (q + ε) 0) ^ 2 / d) ≤
      Real.exp (2 * E + κ * E ^ 2) *
        Real.exp (-2 * q - (κ / 2) * (max q 0) ^ 2 / d) := by
  have hs : q - E ≤ max (q + ε) 0 := by
    have hm := le_max_left (q + ε) 0
    linarith
  have hg := source_upper_gaussian_shift_exponential q (max (q + ε) 0) E κ d
    hE hκ hd hs
  have hl : Real.exp (-2 * (q + ε)) ≤ Real.exp (2 * E - 2 * q) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hm := mul_le_mul hl hg (Real.exp_nonneg _)
    (Real.exp_nonneg (2 * E - 2 * q))
  calc
    _ = Real.exp (-2 * (q + ε)) *
        Real.exp (-(κ * (max (q + ε) 0) ^ 2 / d)) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    _ ≤ Real.exp (2 * E - 2 * q) *
        (Real.exp (κ * E ^ 2) * Real.exp (-((κ / 2) * (max q 0) ^ 2 / d))) := hm
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1 <;> ring

end SRWTightness
