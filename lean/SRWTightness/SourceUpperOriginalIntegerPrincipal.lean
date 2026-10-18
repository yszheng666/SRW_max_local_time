import SRWTightness.SourceUpperOriginalPrincipalFamily
import SRWTightness.SourceUpperIntegerWindowSummable
import SRWTightness.SourceUpperIntegerWindowInfiniteBound

open Filter

namespace SRWTightness

/-- The manuscript integer-window series is nonnegative, including empty coarse root levels. -/
theorem source_upper_integer_window_series_nonneg (t s c L : ℝ)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t)) :
    0 ≤ sourceUpperIntegerWindowSeries t s c L := by
  unfold sourceUpperIntegerWindowSeries
  apply tsum_nonneg
  intro n
  apply source_upper_integer_window_kernel_nonneg t s c L _ hd
  have ha := Int.le_ceil (-(7 + s +
    upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)))
  simp only [Int.cast_add, Int.cast_natCast]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Every actual root-level principal contribution obeys the original infinite integer formula. -/
theorem source_upper_original_integer_principal (K κ : ℝ)
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
            sourceUpperIntegerWindowSeries t s (κ / 4) L := by
  obtain ⟨D, hD, hfamily⟩ := source_upper_original_principal_family K κ hK hκ.le
  refine ⟨D * Real.exp (2 + κ / 2), by positivity, ?_⟩
  filter_upwards [hfamily, source_upper_integer_window_summable (κ / 4) (by positivity),
    source_upper_branching_depth_bounds,
    source_upper_terminal_sqrt_scale exponential_floor_scale_input,
    eventually_ge_atTop (2 : ℝ)] with t ht hsum hdepth hd ht2
  intro s hs hslog B C hB hC M k
  dsimp only
  let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  have hd0 : 0 < d := Real.sqrt_pos.mp (by linarith [hd.1])
  have hd1 : 1 ≤ d := by nlinarith [Real.sq_sqrt hd0.le, hd.1]
  have hseries := source_upper_integer_window_series_nonneg t s (κ / 4) L hd0.le
  classical
  by_cases hempty : sourceUpperBlockRootFamily t k = ∅
  · simp only [hempty, Finset.sum_empty]
    change 0 ≤ _ * sourceUpperIntegerWindowSeries t s (κ / 4) L
    exact mul_nonneg (by positivity) hseries
  · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hb, hk⟩ := Finset.mem_filter.mp hb
    have hL : 0 < L := by
      dsimp [L]
      rw [← hk]
      exact_mod_cast Nat.sub_pos_of_lt (hdepth b hb).1
    have hconv := hsum b hb s hs hslog
    rw [hk] at hconv
    have hfinite := source_upper_integer_window_infinite_bound t s κ L ht2 hκ.le hd1 hL
      hconv
    have hprincipal := ht s hs hslog B C hB hC M k
      (sourceUpperSupportedWindowIndices t s) (fun i hi ↦ (Finset.mem_filter.mp hi).2.2)
    have hP : 0 ≤ D * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
        Real.exp (2 * t - 2 * d) / L ^ 2 := by positivity
    exact hprincipal.trans ((mul_le_mul_of_nonneg_left hfinite hP).trans_eq (by
      dsimp [L, d]
      ring))

end SRWTightness
