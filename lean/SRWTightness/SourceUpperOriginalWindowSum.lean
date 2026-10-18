import SRWTightness.SourceUpperWindowOriginalGaussian
import SRWTightness.SourceUpperRootWeightedWindow
import SRWTightness.SourceUpperRootTerminalNormalized
import SRWTightness.SourceUpperTerminalSqrtScale
import SRWTightness.ExponentialFloorScaleProof

open Filter

namespace SRWTightness

/-- The literal supported original-Gaussian window kernel, before completing its square. -/
noncomputable def sourceUpperOriginalGaussianWindowKernel (t s κ L u : ℝ) : ℝ :=
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let q := x - u
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  (S + q) / d * (1 + max q 0 / Real.sqrt d) *
    Real.exp (-(x - q) ^ 2 / (2 * L) - 2 * q - (κ / 2) * (max q 0) ^ 2 / d)

/-- Root-population summation retains the original terminal-window sum and Gaussian square. -/
theorem source_upper_original_window_sum (K κ : ℝ) (hK : 1 ≤ K) (hκ : 0 ≤ κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
      ∀ M : ℕ, ∀ I : Finset ℕ,
      let k := sourceUpperBlockRoot t b
      let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      (∀ i ∈ I, t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) →
      sourceUpperRootTerminalContribution t s K κ B C b M I ≤
        D * B * C * (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k) *
          r ^ 2 * Real.exp (-2 * d) / L ^ 2 *
            ∑ i ∈ I, sourceUpperOriginalGaussianWindowKernel t s κ L (t - 1 + (i : ℝ)) := by
  obtain ⟨Cr, hCr, hr⟩ := source_upper_root_weighted_window exponential_floor_scale_input K hK
  refine ⟨Cr * Real.exp (2 + κ), by positivity, ?_⟩
  filter_upwards [hr, source_upper_terminal_sqrt_scale exponential_floor_scale_input]
    with t ht hd
  intro b hb s hs hslog B C hB hC M I
  dsimp only
  intro hI
  let k := sourceUpperBlockRoot t b
  let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let u := fun i : ℕ ↦ t - 1 + (i : ℝ)
  let W := fun i : ℕ ↦ sourceUpperTerminalWindowWeight t s C κ (u i)
  let P := B * (5 + s + (k : ℝ)) / L ^ 2 *
    (Cr * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * k))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hdpos : 0 < d := Real.sqrt_pos.mp (by linarith [hd.1])
  have hd1 : 1 ≤ d := by
    have hsq := Real.sq_sqrt hdpos.le
    nlinarith [hd.1]
  have hW (i : ℕ) : 0 ≤ W i := by
    dsimp [W, sourceUpperTerminalWindowWeight]
    positivity
  have hroot (i : ℕ) (hi : i ∈ I) :
      (∑ J ∈ Finset.range M, (1 - 1 / ((k : ℝ) + K)) ^ (J - 1) *
        sourceUpperBranchingWindowFactor t s B k J (u i)) ≤
      P * (sourceUpperBranchingSlack t s (u i) * Real.exp (-(u i) ^ 2 / (2 * L))) := by
    have hh := ht b hb s hs hslog (u i)
      (by dsimp [u]; linarith [Nat.cast_nonneg (α := ℝ) i]) (hI i hi) B hB M
    exact hh.trans_eq (by dsimp [P, L, k]; ring)
  have hwindow (i : ℕ) (hi : i ∈ I) :
      W i * (sourceUpperBranchingSlack t s (u i) * Real.exp (-(u i) ^ 2 / (2 * L))) ≤
      (C * r ^ 2 * Real.exp (-2 * d) * Real.exp (2 + κ)) *
        sourceUpperOriginalGaussianWindowKernel t s κ L (u i) :=
    source_upper_window_original_gaussian t s C κ (u i) L hC hκ hd1 (hI i hi)
  calc
    _ = ∑ i ∈ I, W i * ∑ J ∈ Finset.range M,
        (1 - 1 / ((k : ℝ) + K)) ^ (J - 1) *
          sourceUpperBranchingWindowFactor t s B k J (u i) := by
      unfold sourceUpperRootTerminalContribution
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
      Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hroot i hi) (hW i))
    _ = P * ∑ i ∈ I, W i *
        (sourceUpperBranchingSlack t s (u i) * Real.exp (-(u i) ^ 2 / (2 * L))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ ↦ by ring)
    _ ≤ P * ∑ i ∈ I, (C * r ^ 2 * Real.exp (-2 * d) * Real.exp (2 + κ)) *
        sourceUpperOriginalGaussianWindowKernel t s κ L (u i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hwindow) hP
    _ = _ := by
      rw [← Finset.mul_sum]
      dsimp [P, k, L, r, d, u]
      ring

end SRWTightness
