import SRWTightness.SourceUpperTerminalWindowProduct
import SRWTightness.SourceUpperTerminalFiniteSum

open Filter

namespace SRWTightness

/-- Summing actual supported terminal weights preserves the baseline remaining-depth Gaussian. -/
theorem source_upper_terminal_weighted_sum (hScale : ExponentialFloorScaleInput)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ C : ℝ, 0 ≤ C → ∀ I : Finset ℕ,
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let r := upperTerminalFineRadius (sourceUpperLogRadius t)
      let x := sourceUpperTarget t s
      let L : ℝ := (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ)
      (∀ i ∈ I, -(7 + s + d ^ (1 / 4 : ℝ)) ≤ x - (t - 1 + (i : ℝ)) ∧
        t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) →
      (∑ i ∈ I, sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) *
        (sourceUpperBranchingSlack t s (t - 1 + (i : ℝ)) *
          Real.exp (-(t - 1 + (i : ℝ)) ^ 2 / (2 * L)))) ≤
        K * C * r ^ 2 * Real.exp (-2 * d) * Real.exp (-x ^ 2 / (2 * L)) := by
  obtain ⟨K, hK, hfinite⟩ := source_upper_terminal_finite_sum hScale κ hκ
  refine ⟨Real.exp 2 * K, by positivity, ?_⟩
  filter_upwards [hfinite, source_upper_terminal_sqrt_scale hScale,
    source_upper_branching_depth_bounds, eventually_ge_atTop (1 : ℝ)] with t ht hd hdepth ht1
  intro b hb s hs hslog C hC I
  dsimp only
  intro hI
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let L : ℝ := (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ)
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  let v := x - (t - 1)
  let F := fun q : ℝ ↦ (S + q) * (1 + max q 0 / Real.sqrt d) / d *
    Real.exp ((x / L - 2) * q - κ * (max (q - 1) 0) ^ 2 / d)
  let E := C * r ^ 2 * Real.exp (-2 * d) * Real.exp 2 * Real.exp (-x ^ 2 / (2 * L))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hL : 0 < L := by dsimp [L]; linarith [(hdepth b hb).2.1]
  have hd0 : 0 < d := Real.sqrt_pos.mp (by linarith [hd.1])
  have he (i : ℕ) : v - (i : ℝ) = x - (t - 1 + (i : ℝ)) := by dsimp [v]; ring
  have hsum : (∑ i ∈ I, F (v - (i : ℝ))) ≤ K := by
    apply ht b hb s hs hslog v I
    intro i hi
    rw [he]
    exact (hI i hi).1
  have hpoint (i : ℕ) (hi : i ∈ I) :
      sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) *
        (sourceUpperBranchingSlack t s (t - 1 + (i : ℝ)) *
          Real.exp (-(t - 1 + (i : ℝ)) ^ 2 / (2 * L))) ≤ E * F (v - (i : ℝ)) := by
    rw [he]
    exact source_upper_terminal_window_product t s C κ (t - 1 + (i : ℝ)) L
      hC hL hd0 (hI i hi).2
  calc
    _ ≤ ∑ i ∈ I, E * F (v - (i : ℝ)) := Finset.sum_le_sum hpoint
    _ = E * ∑ i ∈ I, F (v - (i : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ E * K := mul_le_mul_of_nonneg_left hsum hE
    _ = _ := by dsimp [E, x, r, d, L]; ring

end SRWTightness
