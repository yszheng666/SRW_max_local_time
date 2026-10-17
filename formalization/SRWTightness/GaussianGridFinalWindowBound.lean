import SRWTightness.GaussianGridTerminalEventLaw

namespace SRWTightness

/-- The full terminal event bounds the final increment by the endpoint offset and window errors. -/
theorem gaussianGrid_final_window_bound (T : ℕ → ℝ) (n : ℕ)
    (At V d q a ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hAt : |At - (2 * d + q)| ≤ ε) (hV : |V - d| ≤ K)
    (γ : ℝ) (p : (Fin (n + 1) → ℝ) × (ℕ → GaussianCoefficientSpace))
    (hp : p ∈ gaussianGridTerminalEvent T n (q - a - 1) (q - a) At V q d γ) :
    |gaussianGridFinalIncrement T n p| ≤ |a| + 2 + ε + 2 * K ∧
      (gaussianGridFinalIncrement T n p) ^ 2 ≤ (|a| + 2 + ε + 2 * K) ^ 2 := by
  have hz := source_site_increment_window_location At V d q a
    (gaussianGridPath T n p (T n)) ε K hAt hV hp.1.1
  have hi := (gaussianGrid_site_window_increment T n At V p).mp hp.2
  have hab : |gaussianGridFinalIncrement T n p| ≤ |a| + 2 + ε + 2 * K := by
    apply abs_le.mpr
    constructor
    · linarith [hz.1, hi.1, neg_abs_le a]
    · linarith [hz.2, hi.2, le_abs_self a]
  refine ⟨hab, ?_⟩
  have hh := sq_le_sq₀ (abs_nonneg (gaussianGridFinalIncrement T n p))
    (by positivity : 0 ≤ |a| + 2 + ε + 2 * K)
  simpa only [sq_abs] using hh.mpr hab

end SRWTightness
