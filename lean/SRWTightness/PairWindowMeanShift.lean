import SRWTightness.PairWindows

namespace SRWTightness

theorem pairDeficitWindow_lower (top : ℝ) (l : ℕ) (s : ℝ)
    (hs : s ∈ pairDeficitWindow top l) : top - l - 1 ≤ s := by
  unfold pairDeficitWindow at hs
  split at hs
  · rename_i hl
    subst l
    simpa using hs.1
  · exact hs.1

/-- Centering the last Gaussian average shifts its deficit window by twice the discrete error. -/
theorem pairWindow_centered_last {N : ℕ} (last : Fin N)
    (m x : PairObservationIndex N → ℝ) (At v q f e : ℝ) (n p l : ℕ)
    (hm : m (.inl last) = 2 * v + 2 * e)
    (hx : m + x ∈ pairWindow last At (2 * v + q - f) n p l) :
    x (.inl last) ∈ Set.Icc (q - f - l - 1 - 2 * e) (q - f - l - 2 * e) := by
  have hlo := pairDeficitWindow_lower _ _ _ hx.2.2
  have hhi := pairDeficitWindow_upper _ _ _ hx.2.2
  simp only [Pi.add_apply, hm] at hlo hhi
  constructor <;> linarith

end SRWTightness
