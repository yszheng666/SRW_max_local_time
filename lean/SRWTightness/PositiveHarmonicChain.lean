import SRWTightness.ExternalPositiveHarmonic
import SRWTightness.RelativeProbabilityExponential

namespace SRWTightness

/-- The original relative harmonic input gives multiplicative bounds along any admissible chain. -/
theorem positive_harmonic_chain (hinput : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 8 ≤ B → 2 * C ≤ B →
      ∀ (f : Site → ℝ), (∀ y, 0 ≤ f y) → ∀ (x : ℕ → Site) (n : ℕ),
      (∀ i < n, normSq (x (i + 1) - x i) < 4) →
      (∀ i < n, ∀ y ∈ translateFinset (x i) (diskFinset B),
        f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) →
      Real.exp (-(2 * (C / B) * (n : ℝ))) * f (x 0) ≤ f (x n) ∧
        f (x n) ≤ Real.exp (2 * (C / B) * (n : ℝ)) * f (x 0) := by
  obtain ⟨C, hC, hh⟩ := hinput
  refine ⟨C, hC, ?_⟩
  intro B hB hCB f hf x n
  have hB0 : 0 < B := by linarith
  have hε : 0 ≤ C / B := div_nonneg hC.le hB0.le
  have hsmall : C / B ≤ 1 / 2 := (div_le_iff₀ hB0).mpr (by linarith)
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
    intro hstep hharm
    have hi := ih (fun i hi ↦ hstep i (by omega)) (fun i hi ↦ hharm i (by omega))
    have hx : x (n + 1) ∈ translateFinset (x n) (diskFinset (2 * (1 : ℝ))) := by
      rw [mem_translateFinset_iff, mem_diskFinset]
      simpa only [disk, Set.mem_setOf_eq, mul_one, show (2 : ℝ) ^ 2 = 4 by norm_num] using
        hstep n (by omega)
    have hr := hh (x n) 1 B le_rfl (by simpa using hB) f hf
      (hharm n (by omega)) (x (n + 1)) hx
    simp only [one_div] at hr
    have hp : |f (x (n + 1)) - f (x n)| ≤ (C / B) * f (x n) := by
      simpa only [div_eq_mul_inv, mul_assoc] using hr
    have he := relative_probability_exponential _ _ _ (hf (x n)) hε hsmall hp
    constructor
    · calc
        _ = Real.exp (-(2 * (C / B))) *
            (Real.exp (-(2 * (C / B) * (n : ℝ))) * f (x 0)) := by
          rw [Nat.cast_succ, show -(2 * (C / B) * ((n : ℝ) + 1)) =
            -(2 * (C / B)) + -(2 * (C / B) * (n : ℝ)) by ring, Real.exp_add]
          ring
        _ ≤ Real.exp (-(2 * (C / B))) * f (x n) :=
          mul_le_mul_of_nonneg_left hi.1 (Real.exp_nonneg _)
        _ ≤ _ := he.1
    · calc
        _ ≤ Real.exp (2 * (C / B)) * f (x n) := he.2
        _ ≤ Real.exp (2 * (C / B)) *
            (Real.exp (2 * (C / B) * (n : ℝ)) * f (x 0)) :=
          mul_le_mul_of_nonneg_left hi.2 (Real.exp_nonneg _)
        _ = _ := by
          rw [Nat.cast_succ, show 2 * (C / B) * ((n : ℝ) + 1) =
            2 * (C / B) + 2 * (C / B) * (n : ℝ) by ring, Real.exp_add]
          ring

end SRWTightness
