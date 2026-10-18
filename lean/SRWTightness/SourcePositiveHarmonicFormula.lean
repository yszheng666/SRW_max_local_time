import SRWTightness.ExternalPositiveHarmonic

namespace SRWTightness

/-- Source (2.13), including the closed interior boundary and zero central-value case. -/
theorem source_positive_harmonic_formula (hH : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : Site) (A B : ℝ), 1 ≤ A → 16 * A ≤ B →
      ∀ f : Site → ℝ, (∀ y, 0 ≤ f y) →
      (∀ y ∈ translateFinset b (diskFinset B),
        f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) →
      ∀ x : Site, normSq (x - b) ≤ (2 * A) ^ 2 →
        |f x - f b| ≤ C * (A / B) * f b ∧
        ∃ ε : ℝ, |ε| ≤ C * (A / B) ∧ f x = f b * (1 + ε) := by
  obtain ⟨C, hC, hh⟩ := hH
  refine ⟨2 * C, by positivity, ?_⟩
  intro b A B hA hAB f hnonneg hharm x hx
  have hxin : x ∈ translateFinset b (diskFinset (2 * (2 * A))) := by
    rw [mem_translateFinset_iff, mem_diskFinset]
    change normSq (x - b) < (2 * (2 * A)) ^ 2
    nlinarith
  have hb := hh b (2 * A) B (by linarith) (by linarith) f hnonneg hharm x hxin
  have hbound : |f x - f b| ≤ (2 * C) * (A / B) * f b := by
    convert hb using 1 <;> ring
  refine ⟨hbound, ?_⟩
  by_cases hf : f b = 0
  · have hfx : f x = 0 := by
      rw [hf, sub_zero, mul_zero] at hbound
      exact abs_eq_zero.mp ((abs_nonneg _).antisymm hbound).symm
    refine ⟨0, ?_, ?_⟩
    · simp only [abs_zero]
      exact mul_nonneg (by positivity) (div_nonneg (by linarith) (by linarith))
    · simp [hf, hfx]
  · have hfb : 0 < f b := lt_of_le_of_ne (hnonneg b) (Ne.symm hf)
    refine ⟨(f x - f b) / f b, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hfb]
      exact (div_le_iff₀ hfb).mpr hbound
    · field_simp
      <;> ring

end SRWTightness
