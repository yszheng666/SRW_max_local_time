import Mathlib.Tactic

namespace SRWTightness

/-- All quantitative comparison thresholds follow from a fixed large ratio m/H. -/
theorem source_comparison_scale_threshold (B T M A : ℝ)
    (hB : 0 ≤ B) (hT : 2 ≤ T) (hM : 128 ≤ M) (hA : 2 ≤ A) :
    ∃ S : ℝ, 128 ≤ S ∧ ∀ H m : ℝ, 1 ≤ H → S * H ≤ m →
      8 * H ≤ m ∧ T ≤ m - H ∧ M ≤ m ∧
        B * H / m ≤ 1 / 4 ∧ A ≤ m - H := by
  let S := 8 + 4 * B + 2 * T + M + 2 * A
  have hS : 128 ≤ S := by dsimp [S]; linarith
  refine ⟨S, hS, ?_⟩
  intro H m hH hm
  have hH0 : 0 ≤ H := by linarith
  have hSm : S ≤ m := (le_mul_of_one_le_right (by linarith) hH).trans hm
  have h8 : 8 * H ≤ m :=
    (mul_le_mul_of_nonneg_right (show 8 ≤ S by dsimp [S]; linarith) hH0).trans hm
  have h4 : (4 * B) * H ≤ m :=
    (mul_le_mul_of_nonneg_right (show 4 * B ≤ S by dsimp [S]; linarith) hH0).trans hm
  have hT₂ : 2 * T ≤ m := (show 2 * T ≤ S by dsimp [S]; linarith).trans hSm
  have hA₂ : 2 * A ≤ m := (show 2 * A ≤ S by dsimp [S]; linarith).trans hSm
  have hMm : M ≤ m := (show M ≤ S by dsimp [S]; linarith).trans hSm
  refine ⟨h8, by linarith, hMm, ?_, by linarith⟩
  apply (div_le_iff₀ (by linarith : 0 < m)).mpr
  nlinarith

end SRWTightness
