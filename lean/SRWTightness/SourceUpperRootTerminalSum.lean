import SRWTightness.SourceUpperTerminalWeightedSum
import SRWTightness.SourceUpperRootWeightedWindow

open Filter

namespace SRWTightness

/-- The actual finite root-population and supported terminal-window sums combine explicitly. -/
theorem source_upper_root_terminal_sum (hScale : ExponentialFloorScaleInput)
    (K κ : ℝ) (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
      ∀ M : ℕ, ∀ I : Finset ℕ,
      let k := sourceUpperBlockRoot t b
      let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      let x := sourceUpperTarget t s
      (∀ i ∈ I, -(7 + s + d ^ (1 / 4 : ℝ)) ≤ x - (t - 1 + (i : ℝ)) ∧
        t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) →
      (∑ J ∈ Finset.range M, (1 - 1 / ((k : ℝ) + K)) ^ (J - 1) *
        ∑ i ∈ I, sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) *
          sourceUpperBranchingWindowFactor t s B k J (t - 1 + (i : ℝ))) ≤
      D * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k) *
        r ^ 2 * Real.exp (-2 * d - x ^ 2 / (2 * L)) / L ^ 2 := by
  obtain ⟨Cr, hCr, hr⟩ := source_upper_root_weighted_window hScale K hK
  obtain ⟨Ct, hCt, ht⟩ := source_upper_terminal_weighted_sum hScale κ hκ
  refine ⟨Cr * Ct, by positivity, ?_⟩
  filter_upwards [hr, ht, source_upper_terminal_sqrt_scale hScale] with t hroot hterm hd
  intro b hb s hs hslog B C hB hC M I
  dsimp only
  intro hI
  let k := sourceUpperBlockRoot t b
  let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let u := fun i : ℕ ↦ t - 1 + (i : ℝ)
  let W := fun i : ℕ ↦ sourceUpperTerminalWindowWeight t s C κ (u i)
  let P := B * (5 + s + (k : ℝ)) / L ^ 2 *
    (Cr * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hd0 : 0 < d := Real.sqrt_pos.mp (by linarith [hd.1])
  have hW (i : ℕ) : 0 ≤ W i := by
    dsimp [W, sourceUpperTerminalWindowWeight]
    positivity
  have hri (i : ℕ) (hi : i ∈ I) :
      (∑ J ∈ Finset.range M, (1 - 1 / ((k : ℝ) + K)) ^ (J - 1) *
        sourceUpperBranchingWindowFactor t s B k J (u i)) ≤
      P * (sourceUpperBranchingSlack t s (u i) * Real.exp (-(u i) ^ 2 / (2 * L))) := by
    have hh := hroot b hb s hs hslog (u i)
      (by dsimp [u]; linarith [Nat.cast_nonneg (α := ℝ) i]) (hI i hi).2 B hB M
    exact hh.trans_eq (by dsimp [P, L, k]; ring)
  have hsum := hterm b hb s hs hslog C hC I hI
  have he : Real.exp (-2 * d - x ^ 2 / (2 * L)) =
      Real.exp (-2 * d) * Real.exp (-x ^ 2 / (2 * L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ∑ i ∈ I, W i * ∑ J ∈ Finset.range M,
        (1 - 1 / ((k : ℝ) + K)) ^ (J - 1) *
          sourceUpperBranchingWindowFactor t s B k J (u i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro J hJ
      dsimp [W, u, k]
      ring
    _ ≤ ∑ i ∈ I, W i * (P *
        (sourceUpperBranchingSlack t s (u i) * Real.exp (-(u i) ^ 2 / (2 * L)))) :=
      Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hri i hi) (hW i))
    _ = P * ∑ i ∈ I, W i *
        (sourceUpperBranchingSlack t s (u i) * Real.exp (-(u i) ^ 2 / (2 * L))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ ↦ by ring)
    _ ≤ P * (Ct * C * r ^ 2 * Real.exp (-2 * d) * Real.exp (-x ^ 2 / (2 * L))) :=
      mul_le_mul_of_nonneg_left hsum hP
    _ = _ := by
      change P * (Ct * C * r ^ 2 * Real.exp (-2 * d) * Real.exp (-x ^ 2 / (2 * L))) =
        (Cr * Ct) * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
          Real.exp (2 * k) * r ^ 2 * Real.exp (-2 * d - x ^ 2 / (2 * L)) / L ^ 2
      rw [he]
      dsimp [P]
      ring

end SRWTightness
