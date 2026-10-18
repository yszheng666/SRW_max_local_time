import SRWTightness.SourceUpperOriginalIntegerPrincipal
import SRWTightness.SourceUpperLiteralIntegerSeries

open Filter

namespace SRWTightness

/-- The actual root-level principal contribution satisfies the literal original (4.29) sum. -/
theorem source_upper_literal_integer_principal (K κ : ℝ)
    (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C → ∀ M k : ℕ,
      let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      (∑ b ∈ sourceUpperBlockRootFamily t k,
        sourceUpperRootTerminalContribution t s K κ B C b M
          (sourceUpperSupportedWindowIndices t s)) ≤
        D * B * C * (1 + (4 + s) + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
          Real.exp (2 * t - 2 * d) / L ^ 2 *
            sourceUpperLiteralIntegerSeries t s (κ / 4) L := by
  obtain ⟨D, hD, hprincipal⟩ := source_upper_original_integer_principal K κ hK hκ
  refine ⟨4 * D, by positivity, ?_⟩
  filter_upwards [hprincipal, source_upper_integer_window_summable (κ / 4) (by positivity),
    source_upper_terminal_sqrt_scale exponential_floor_scale_input,
    source_upper_terminal_quarter_depth_eventually] with t ht hsum hd hr
  intro s hs hslog B C hB hC M k
  dsimp only
  let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  have hd0 : 0 ≤ d := (Real.sqrt_pos.mp (by linarith [hd.1])).le
  have hnew := source_upper_literal_integer_series_nonneg t s (κ / 4) L hd0 hr
  classical
  by_cases hempty : sourceUpperBlockRootFamily t k = ∅
  · simp only [hempty, Finset.sum_empty]
    change 0 ≤ _ * sourceUpperLiteralIntegerSeries t s (κ / 4) L
    exact mul_nonneg (by positivity) hnew
  · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hb, hk⟩ := Finset.mem_filter.mp hb
    have hconv := hsum b hb s hs hslog
    rw [hk] at hconv
    have hbound := (source_upper_literal_integer_series_bounds t s (κ / 4) L hd0 hr hconv).2
    have hP : 0 ≤ D * B * C * (1 + (4 + s) + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
        Real.exp (2 * t - 2 * d) / L ^ 2 := by positivity
    exact (ht s hs hslog B C hB hC M k).trans
      ((mul_le_mul_of_nonneg_left hbound hP).trans_eq (by dsimp [L, d]; ring))

/-- The retained quadratic deficit decay in the literal principal formula is strictly positive. -/
theorem source_upper_literal_integer_decay_pos (κ : ℝ) (hκ : 0 < κ) : 0 < κ / 4 := by
  positivity

end SRWTightness
