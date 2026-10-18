import SRWTightness.GeometricTerminalIndex
import SRWTightness.DiskGaussianParameterChoice

namespace SRWTightness

/-- The first geometric radius above 4ρ stays within one geometric factor of 4ρ. -/
theorem first_pair_observation_index (A B ρ : ℝ) (I : ℕ)
    (hA : 0 < A) (hB : 1 < B) (hρ : A < ρ) (hcover : 4 * ρ ≤ A * B ^ I) :
    ∃ i : ℕ, i ≤ I ∧ 4 * ρ ≤ A * B ^ i ∧ A * B ^ i ≤ 4 * B * ρ ∧
      ∀ j : ℕ, j < i → A * B ^ j < 4 * ρ := by
  have hex : ∃ i : ℕ, 4 * ρ ≤ A * B ^ i := ⟨I, hcover⟩
  let i := Nat.find hex
  have hi : 4 * ρ ≤ A * B ^ i := Nat.find_spec hex
  have hmin (j : ℕ) (hj : j < i) : A * B ^ j < 4 * ρ :=
    lt_of_not_ge (Nat.find_min hex hj)
  have hi0 : 0 < i := by
    by_contra hn
    have hz : i = 0 := by omega
    rw [hz, pow_zero, mul_one] at hi
    linarith
  have hprev := hmin (i - 1) (by omega)
  have hupper : A * B ^ i ≤ 4 * B * ρ := by
    have he : i - 1 + 1 = i := by omega
    have hh := mul_le_mul_of_nonneg_right hprev.le (by linarith : 0 ≤ B)
    rw [mul_assoc, ← pow_succ, he] at hh
    nlinarith
  exact ⟨i, Nat.find_min' hex hcover, hi, hupper, hmin⟩

/-- The actual late-pair distance range guarantees that the first covering radius is retained. -/
theorem source_pair_observation_index (A ρ : ℝ) (I : ℕ)
    (hA : 0 < A) (hρ : A < ρ)
    (hcut : ρ ≤ A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio)) :
    ∃ i : ℕ, i ≤ I ∧ 4 * ρ ≤ A * diskEnergyGapRatio ^ i ∧
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * ρ ∧
      ∀ j : ℕ, j < i → A * diskEnergyGapRatio ^ j < 4 * ρ := by
  have hB := diskEnergyGapRatio_gt_four
  have hm := (le_div_iff₀ (by linarith : 0 < 8 * diskEnergyGapRatio)).mp hcut
  apply first_pair_observation_index A diskEnergyGapRatio ρ I hA (by linarith) hρ
  nlinarith

end SRWTightness
