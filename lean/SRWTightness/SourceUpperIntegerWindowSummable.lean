import SRWTightness.SourceUpperIntegerWindowSupport
import SRWTightness.SourceUpperTerminalInfiniteSum
import SRWTightness.ExponentialFloorScaleProof

open Filter

namespace SRWTightness

/-- The original Gaussian integer ray converges for each actual coarse root family. -/
theorem source_upper_integer_window_summable (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      let L : ℝ := (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ)
      let Q := 7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)
      Summable (fun n : ℕ ↦ sourceUpperIntegerWindowKernel t s c L (⌈-Q⌉ + n)) := by
  obtain ⟨C, hC, hsum⟩ := source_upper_terminal_infinite_sum
    exponential_floor_scale_input c hc
  filter_upwards [hsum, source_upper_branching_depth_bounds,
    source_upper_terminal_sqrt_scale exponential_floor_scale_input] with t ht hdepth hd
  intro b hb s hs hslog
  dsimp only
  let L : ℝ := (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ)
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let Q := 7 + s + d ^ (1 / 4 : ℝ)
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  let a : ℝ := (⌈-Q⌉ : ℤ)
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast Nat.sub_pos_of_lt (hdepth b hb).1
  have hd0 : 0 < d := Real.sqrt_pos.mp (by linarith [hd.1])
  have ha : -Q ≤ a := Int.le_ceil _
  have htilt := (ht b hb s hs hslog a ha).1
  let F := fun n : ℕ ↦ Real.exp (-x ^ 2 / (2 * L)) *
    ((S + (a + (n : ℝ))) * (1 + max (a + (n : ℝ)) 0 / Real.sqrt d) / d *
      Real.exp ((x / L - 2) * (a + (n : ℝ)) -
        c * (max (a + (n : ℝ)) 0) ^ 2 / d))
  have hF : Summable F := htilt.mul_left _
  apply Summable.of_nonneg_of_le _ _ hF
  · intro n
    exact source_upper_integer_window_kernel_nonneg t s c L _ hd0.le (by
      simp only [Int.cast_add, Int.cast_natCast]
      linarith [Nat.cast_nonneg (α := ℝ) n])
  · intro n
    let q : ℝ := a + n
    have hq : ((⌈-Q⌉ + (n : ℤ) : ℤ) : ℝ) = q := by
      simp [q, a]
    have hSq : 0 ≤ S + q := by
      have hr := Real.rpow_nonneg hd0.le (1 / 4 : ℝ)
      dsimp [S, q, Q] at *
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have he : -(x - q) ^ 2 / (2 * L) - 2 * q - c * (max q 0) ^ 2 / d ≤
        -x ^ 2 / (2 * L) + ((x / L - 2) * q - c * (max q 0) ^ 2 / d) := by
      have hid : -(x - q) ^ 2 / (2 * L) - 2 * q =
          -x ^ 2 / (2 * L) + (x / L - 2) * q - q ^ 2 / (2 * L) := by
        field_simp
        <;> ring
      rw [hid]
      have hn : 0 ≤ q ^ 2 / (2 * L) := by positivity
      linarith
    change sourceUpperIntegerWindowKernel t s c L (⌈-Q⌉ + n) ≤ F n
    unfold sourceUpperIntegerWindowKernel
    rw [hq]
    dsimp only [F]
    change (S + q) / d * (1 + max q 0 / Real.sqrt d) *
      Real.exp (-(x - q) ^ 2 / (2 * L) - 2 * q - c * (max q 0) ^ 2 / d) ≤ _
    calc
      _ ≤ (S + q) / d * (1 + max q 0 / Real.sqrt d) *
          Real.exp (-x ^ 2 / (2 * L) + ((x / L - 2) * q -
            c * (max q 0) ^ 2 / d)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
      _ = _ := by rw [Real.exp_add]; dsimp [q]; ring

end SRWTightness
