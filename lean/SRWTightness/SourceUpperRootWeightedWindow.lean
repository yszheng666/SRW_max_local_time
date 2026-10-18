import SRWTightness.SourceUpperRootSum
import SRWTightness.SourceUpperTerminalWindowProbability

open Filter

namespace SRWTightness

/-- The geometric root sum removes the root population from each actual branching window. -/
theorem source_upper_root_weighted_window (hScale : ExponentialFloorScaleInput)
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ u : ℝ,
      t - 1 ≤ u → u ≤ sourceUpperBranchingEnd t s → ∀ B : ℝ, 0 ≤ B → ∀ M : ℕ,
      let k := sourceUpperBlockRoot t b
      let L := sourceUpperCoarseDepth t - k
      (∑ J ∈ Finset.range M, (1 - 1 / ((k : ℝ) + K)) ^ (J - 1) *
        sourceUpperBranchingWindowFactor t s B k J u) ≤
      (B * (5 + s + k) * sourceUpperBranchingSlack t s u / (L : ℝ) ^ 2 *
        Real.exp (-u ^ 2 / (2 * L))) *
          (C * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k)) := by
  obtain ⟨C, hC, hr⟩ := source_upper_root_sum hScale K hK
  refine ⟨C, hC, ?_⟩
  filter_upwards [hr] with t ht
  intro b hb s hs hslog u hu hue B hB M
  dsimp only
  let k := sourceUpperBlockRoot t b
  let L := sourceUpperCoarseDepth t - k
  let P := B * (5 + s + k) * sourceUpperBranchingSlack t s u / (L : ℝ) ^ 2 *
    Real.exp (-u ^ 2 / (2 * L))
  have hslack : 0 ≤ sourceUpperBranchingSlack t s u := by
    unfold sourceUpperBranchingSlack
    linarith
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hq : 1 ≤ (k : ℝ) + K := by
    dsimp [k]
    linarith [Nat.cast_nonneg (α := ℝ) (sourceUpperBlockRoot t b)]
  have hρ : 0 ≤ 1 - 1 / ((k : ℝ) + K) := by
    have hq0 : 0 < (k : ℝ) + K := by linarith
    linarith [(div_le_one hq0).mpr hq]
  have hn (J : ℕ) : 0 ≤ upperGeometricRootTerm ((k : ℝ) + K) (u / L) J := by
    unfold upperGeometricRootTerm
    positivity
  have heq (J : ℕ) : (1 - 1 / ((k : ℝ) + K)) ^ (J - 1) *
      sourceUpperBranchingWindowFactor t s B k J u =
        P * upperGeometricRootTerm ((k : ℝ) + K) (u / L) J := by
    dsimp [P, sourceUpperBranchingWindowFactor, upperGeometricRootTerm, L]
    rw [Real.exp_add]
    ring
  obtain ⟨hsum, hbound⟩ := ht b hb s hs hslog u hu hue
  have hf := hsum.sum_le_tsum (Finset.range M) (fun J _ ↦ hn J)
  calc
    _ = P * ∑ J ∈ Finset.range M, upperGeometricRootTerm ((k : ℝ) + K) (u / L) J := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun J _ ↦ heq J)
    _ ≤ P * (C * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k)) :=
      mul_le_mul_of_nonneg_left (hf.trans hbound) hP

end SRWTightness
