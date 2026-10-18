import SRWTightness.SourceUpperOriginalWindowNonnegative
import SRWTightness.SourceUpperBlockFamilyCount

open Filter

namespace SRWTightness

/-- The actual root-level principal contribution has the original spatial/window expression. -/
theorem source_upper_original_principal_family (K κ : ℝ) (hK : 1 ≤ K) (hκ : 0 ≤ κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C → ∀ M k : ℕ, ∀ I : Finset ℕ,
      let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      (∀ i ∈ I, t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) →
      (∑ b ∈ sourceUpperBlockRootFamily t k,
        sourceUpperRootTerminalContribution t s K κ B C b M I) ≤
        D * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
          Real.exp (2 * t - 2 * d) / L ^ 2 *
            ∑ i ∈ I, sourceUpperOriginalGaussianWindowKernel t s κ L (t - 1 + (i : ℝ)) := by
  obtain ⟨D, hD, hp⟩ := source_upper_original_window_sum K κ hK hκ
  refine ⟨25 * D, by positivity, ?_⟩
  filter_upwards [hp, source_upper_block_family_count,
    source_upper_terminal_sqrt_scale exponential_floor_scale_input] with t ht hc hd
  intro s hs hslog B C hB hC M k I
  dsimp only
  intro hI
  let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let V := ∑ i ∈ I, sourceUpperOriginalGaussianWindowKernel t s κ L (t - 1 + (i : ℝ))
  let W := D * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k) *
    r ^ 2 * Real.exp (-2 * d) / L ^ 2 * V
  have hd0 : 0 ≤ d := (Real.sqrt_pos.mp (by linarith [hd.1])).le
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i hi ↦
    source_upper_original_window_kernel_nonneg t s κ L _ hd0 (hI i hi))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hr : 0 < r := by
    dsimp [r]
    rw [← sourceUpperBlockSide_cast]
    exact_mod_cast sourceUpperBlockSide_pos t
  have hbnd (b : Site) (hb : b ∈ sourceUpperBlockRootFamily t k) :
      sourceUpperRootTerminalContribution t s K κ B C b M I ≤ W := by
    obtain ⟨hb, hk⟩ := Finset.mem_filter.mp hb
    have hh := ht b hb s hs hslog B C hB hC M I hI
    simpa only [hk] using hh
  have he1 : Real.exp (-2 * (k : ℝ)) * Real.exp (2 * k) = 1 := by
    rw [← Real.exp_add]
    rw [show -2 * (k : ℝ) + 2 * k = 0 by ring, Real.exp_zero]
  have he2 : (Real.exp t) ^ 2 * Real.exp (-2 * d) = Real.exp (2 * t - 2 * d) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hrr : r ^ 2 / r ^ 2 = 1 := div_self (pow_ne_zero 2 hr.ne')
  calc
    _ ≤ ∑ b ∈ sourceUpperBlockRootFamily t k, W := Finset.sum_le_sum hbnd
    _ = ((sourceUpperBlockRootFamily t k).card : ℝ) * W := by simp
    _ ≤ (25 * (Real.exp t) ^ 2 * Real.exp (-2 * (k : ℝ)) / r ^ 2) * W :=
      mul_le_mul_of_nonneg_right (hc k) hW
    _ = ((25 * D) * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 / L ^ 2 * V) *
        ((Real.exp t) ^ 2 * Real.exp (-2 * d)) *
        (Real.exp (-2 * (k : ℝ)) * Real.exp (2 * k)) * (r ^ 2 / r ^ 2) := by
      dsimp [W]
      ring
    _ = _ := by
      rw [he1, he2, hrr]
      dsimp [L, d, V]
      ring

end SRWTightness
