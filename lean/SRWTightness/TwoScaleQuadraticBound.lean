import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- A near quadratic estimate and a uniform far bound combine with a scale-independent constant. -/
theorem exists_two_scale_quadratic_constant (δ A B : ℝ) (hδ : 0 < δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧ ∀ (N d U : ℝ), 0 < N → 0 ≤ d → U ≤ B →
      (d ≤ δ * N / 64 → U ≤ A * (d / (δ * N / 8)) ^ 2) → U ≤ L * d ^ 2 / N ^ 2 := by
  let L := 64 * A / δ ^ 2 + 4096 * B / δ ^ 2 + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro N d U hN hd hfar hnear
  have hfactor : 0 ≤ d ^ 2 / N ^ 2 := by positivity
  by_cases hs : d ≤ δ * N / 64
  · have he : A * (d / (δ * N / 8)) ^ 2 = (64 * A / δ ^ 2) * (d ^ 2 / N ^ 2) := by
      field_simp
      <;> ring
    have hb : 64 * A / δ ^ 2 ≤ L := by
      have hp : 0 ≤ 4096 * B / δ ^ 2 := by positivity
      dsimp [L]
      linarith
    calc
      U ≤ _ := hnear hs
      _ = _ := he
      _ ≤ L * (d ^ 2 / N ^ 2) := mul_le_mul_of_nonneg_right hb hfactor
      _ = _ := by ring
  · have hs' : δ * N / 64 ≤ d := (lt_of_not_ge hs).le
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ δ * N / 64) hd).mpr hs'
    have hraw : δ ^ 2 * N ^ 2 ≤ 4096 * d ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hraw hB
    have he : B ≤ (4096 * B / δ ^ 2) * (d ^ 2 / N ^ 2) := by
      calc
        B = (B * (δ ^ 2 * N ^ 2)) / (δ ^ 2 * N ^ 2) := by field_simp
        _ ≤ (4096 * B * d ^ 2) / (δ ^ 2 * N ^ 2) :=
          div_le_div_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by field_simp
    have hb : 4096 * B / δ ^ 2 ≤ L := by
      have hp : 0 ≤ 64 * A / δ ^ 2 := by positivity
      dsimp [L]
      linarith
    calc
      U ≤ B := hfar
      _ ≤ _ := he
      _ ≤ L * (d ^ 2 / N ^ 2) := mul_le_mul_of_nonneg_right hb hfactor
      _ = _ := by ring

end SRWTightness
