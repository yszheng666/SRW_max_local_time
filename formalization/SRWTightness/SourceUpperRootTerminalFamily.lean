import SRWTightness.SourceUpperRootTerminalNormalized
import SRWTightness.SourceUpperBlockFamilyCount

open Filter

namespace SRWTightness

/-- Root-family spatial counting cancels the block-radius and root-population exponential factors. -/
theorem source_upper_root_terminal_family (hScale : ExponentialFloorScaleInput)
    (K κ : ℝ) (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C → ∀ M k : ℕ, ∀ I : Finset ℕ,
      (∀ i ∈ I, -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
        sourceUpperTarget t s - (t - 1 + (i : ℝ)) ∧
        t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) →
      (∑ b ∈ sourceUpperBlockRootFamily t k,
        sourceUpperRootTerminalContribution t s K κ B C b M I) ≤
      D * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
        Real.exp (-(2 * Real.sqrt Real.pi * s)) * Real.exp (-(9 * (k : ℝ) / 8)) := by
  obtain ⟨D, hD, hp⟩ := source_upper_root_terminal_normalized hScale K κ hK hκ
  refine ⟨25 * D, by positivity, ?_⟩
  filter_upwards [hp, source_upper_block_family_count] with t ht hcount
  intro s hs hslog B C hB hC M k I hI
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let W := D * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k) *
    r ^ 2 * Real.exp (-2 * t) * Real.exp (-(2 * Real.sqrt Real.pi * s)) *
    Real.exp (-(9 * (k : ℝ) / 8))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hr : 0 < r := by
    dsimp [r]
    rw [← sourceUpperBlockSide_cast]
    exact_mod_cast sourceUpperBlockSide_pos t
  have hbnd (b : Site) (hb : b ∈ sourceUpperBlockRootFamily t k) :
      sourceUpperRootTerminalContribution t s K κ B C b M I ≤ W := by
    obtain ⟨hb, hk⟩ := Finset.mem_filter.mp hb
    simpa only [hk] using ht b hb s hs hslog B C hB hC M I hI
  have he1 : Real.exp (-2 * (k : ℝ)) * Real.exp (2 * k) = 1 := by
    rw [← Real.exp_add]
    rw [show -2 * (k : ℝ) + 2 * k = 0 by ring, Real.exp_zero]
  have he2 : (Real.exp t) ^ 2 * Real.exp (-2 * t) = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    rw [show t + t + -2 * t = 0 by ring, Real.exp_zero]
  calc
    _ ≤ ∑ b ∈ sourceUpperBlockRootFamily t k, W := Finset.sum_le_sum hbnd
    _ = ((sourceUpperBlockRootFamily t k).card : ℝ) * W := by simp
    _ ≤ (25 * (Real.exp t) ^ 2 * Real.exp (-2 * (k : ℝ)) / r ^ 2) * W :=
      mul_le_mul_of_nonneg_right (hcount k) hW
    _ = ((25 * D) * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
        Real.exp (-(2 * Real.sqrt Real.pi * s)) * Real.exp (-(9 * (k : ℝ) / 8))) *
        ((Real.exp t) ^ 2 * Real.exp (-2 * t)) *
        (Real.exp (-2 * (k : ℝ)) * Real.exp (2 * k)) := by
      dsimp [W]
      field_simp [hr.ne']
      <;> ring
    _ = _ := by rw [he1, he2]; ring

end SRWTightness
