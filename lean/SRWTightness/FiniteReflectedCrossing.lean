import SRWTightness.FiniteFirstCrossing

namespace SRWTightness

/-- A reflected first-crossing endpoint below b forces the original endpoint above 2q-b. -/
theorem reflected_crossing_endpoint_lower (w : ℕ → ℝ) (q b : ℝ) (n k : ℕ)
    (hk : q ≤ w k) (he : 2 * w k - w n ≤ b) : 2 * q - b ≤ w n := by
  linarith

/-- Small grid increments force a sufficiently high endpoint into a reflected crossing event. -/
theorem high_endpoint_reflected_first_crossing (w : ℕ → ℝ) (q b δ : ℝ) (n : ℕ)
    (hzero : w 0 < q) (hb : b < q) (hδ : 0 ≤ δ)
    (hstep : ∀ j < n, w (j + 1) - w j ≤ δ)
    (hend : 2 * (q + δ) - b ≤ w n) :
    ∃ k ≤ n, (q ≤ w k ∧ ∀ j < k, w j < q) ∧ 2 * w k - w n ≤ b := by
  have hn : q ≤ w n := by linarith
  obtain ⟨k, hkn, hk⟩ := finite_first_crossing w q n ⟨n, le_rfl, hn⟩
  have ho := first_crossing_overshoot w q δ n k hzero hkn hk hstep
  exact ⟨k, hkn, hk, by linarith [ho.2.2]⟩

end SRWTightness
