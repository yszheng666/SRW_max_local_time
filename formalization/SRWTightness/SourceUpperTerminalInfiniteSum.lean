import SRWTightness.SourceUpperTerminalFiniteSum
import SRWTightness.UpperTerminalInfiniteGrid

open Filter

namespace SRWTightness

/-- Source (4.32): every admissible unit-grid ray is summable and uniformly bounded. -/
theorem source_upper_terminal_infinite_sum (hScale : ExponentialFloorScaleInput)
    (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ a : ℝ,
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      let β := sourceUpperTarget t s /
        (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) - 2
      let Q := 7 + s + d ^ (1 / 4 : ℝ)
      let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
      let f := fun n : ℕ ↦ (S + (a + (n : ℝ))) *
        (1 + max (a + (n : ℝ)) 0 / Real.sqrt d) / d *
        Real.exp (β * (a + (n : ℝ)) - c * (max (a + (n : ℝ)) 0) ^ 2 / d);
      -Q ≤ a → Summable f ∧ (∑' n : ℕ, f n) ≤ C := by
  obtain ⟨C, hC, hfinite⟩ := source_upper_terminal_finite_sum hScale c hc
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfinite, source_upper_terminal_sqrt_scale hScale] with t ht hscale
  intro b hb s hs hslog a
  dsimp only
  intro ha
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let β := sourceUpperTarget t s /
    (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) - 2
  let Q := 7 + s + d ^ (1 / 4 : ℝ)
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  let f := fun q : ℝ ↦ (S + q) * (1 + max q 0 / Real.sqrt d) / d *
    Real.exp (β * q - c * (max q 0) ^ 2 / d)
  have hsqrt : 1 ≤ Real.sqrt d := hscale.1
  have hd0 : 0 < d := Real.sqrt_pos.mp (by linarith)
  have hr0 : 0 ≤ d ^ (1 / 4 : ℝ) := Real.rpow_nonneg hd0.le _
  have hQS : Q ≤ S := by dsimp [Q, S]; linarith
  have hnonneg (q : ℝ) (hq : -Q ≤ q) : 0 ≤ f q := by
    have hSq : 0 ≤ S + q := by linarith
    dsimp [f]
    positivity
  have hbound (v : ℝ) (I : Finset ℕ) (hq : ∀ J ∈ I, -Q ≤ v - (J : ℝ)) :
      (∑ J ∈ I, f (v - (J : ℝ))) ≤ C := by
    have hh := ht b hb s hs hslog v I hq
    apply le_trans _ hh
    apply Finset.sum_le_sum
    intro J hJ
    let q := v - (J : ℝ)
    have hSq : 0 ≤ S + q := by linarith [hq J hJ]
    have hmax : max (q - 1) 0 ≤ max q 0 := max_le_max (by linarith) le_rfl
    have hmax0 : 0 ≤ max (q - 1) 0 := le_max_right _ _
    have hsq : (max (q - 1) 0) ^ 2 ≤ (max q 0) ^ 2 := by nlinarith
    have hdec := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq hc.le) hd0.le
    change (S + q) * (1 + max q 0 / Real.sqrt d) / d *
      Real.exp (β * q - c * (max q 0) ^ 2 / d) ≤
      (S + q) * (1 + max q 0 / Real.sqrt d) / d *
      Real.exp (β * q - c * (max (q - 1) 0) ^ 2 / d)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  exact upper_terminal_infinite_grid f (-Q) C hnonneg hbound a ha

end SRWTightness
