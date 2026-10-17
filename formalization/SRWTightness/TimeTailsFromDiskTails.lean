import SRWTightness.TimeTailLimsup

open MeasureTheory Filter

namespace SRWTightness

/-- The quantitative deterministic-time tail, conditional on the disk tails only. -/
theorem timeTails_of_diskTails (h : DiskTailClaim) : TimeTailClaim := by
  obtain ⟨C, c, s₀, hC, hc, hs₀, htail⟩ := h
  let κ := Real.log 2 / Real.sqrt Real.pi
  let s₁ := max (2 * s₀) (4 * (κ + 1))
  refine ⟨C, c, s₁, hC, hc, lt_max_of_lt_left (by positivity), ?_⟩
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le (by dsimp [s₁]; exact lt_max_of_lt_left (by positivity)) hs
  have hhalf : s₀ ≤ s / 2 := by have := (le_max_left (2 * s₀) (4 * (κ + 1))).trans hs; linarith
  have hshift : κ + s / 4 + 1 ≤ s / 2 := by
    have := (le_max_right (2 * s₀) (4 * (κ + 1))).trans hs
    linarith
  let A := Real.exp (s * Real.sqrt Real.pi / 8)
  have hA : 1 < A := Real.one_lt_exp_iff.mpr (by positivity)
  have hcenter : ∀ᶠ n : ℕ in atTop,
      |diskCenter (Real.sqrt n / A) - timeCenter n| ≤ s / 2 ∧
      |diskCenter (A * Real.sqrt n) - timeCenter n| ≤ s / 2 := by
    have he : (Real.log 2 + 2 * Real.log A) / Real.sqrt Real.pi + 1 = κ + s / 4 + 1 := by
      dsimp [A, κ]
      rw [Real.log_exp]
      have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
      field_simp
      <;> ring
    filter_upwards [scaled_center_source_eventual A hA] with n hn
    rw [he] at hn
    exact ⟨hn.1.trans hshift, hn.2.trans hshift⟩
  obtain ⟨hu, hl⟩ := htail (s / 2) hhalf
  have hb := time_limsup_tail_le_disk_bounds A (s / 2) (s / 2)
    (C * (1 + s / 2) * Real.exp (-3 * (s / 2) / 2))
    (Real.exp (-c * Real.exp (Real.sqrt Real.pi * (s / 2) / 4))) hA hcenter hu hl
  have hsum : s / 2 + s / 2 = s := by ring
  rw [hsum] at hb
  have he : 2 / A ^ 2 = 2 * Real.exp (-s * Real.sqrt Real.pi / 4) := by
    have hsq : A ^ 2 = Real.exp (s * Real.sqrt Real.pi / 4) := by
      dsimp [A]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hsq, div_eq_mul_inv, ← Real.exp_neg]
    congr 1
    congr 1
    ring
  have hupper : C * (1 + s / 2) * Real.exp (-3 * (s / 2) / 2) ≤
      C * (1 + s) * Real.exp (-3 * s / 4) := by
    rw [show -3 * (s / 2) / 2 = -3 * s / 4 by ring]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith
  rw [he, show Real.sqrt Real.pi * (s / 2) / 4 = Real.sqrt Real.pi * s / 8 by ring] at hb
  linarith

end SRWTightness
