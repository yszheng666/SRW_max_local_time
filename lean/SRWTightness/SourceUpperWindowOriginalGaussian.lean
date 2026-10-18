import SRWTightness.PositiveGaussianUnitShift
import SRWTightness.SourceUpperTerminalWindowProduct

namespace SRWTightness

/-- The actual supported unit-window product retains the original uncompleted Gaussian exponent. -/
theorem source_upper_window_original_gaussian (t s C κ u L : ℝ)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hd : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hu : u ≤ sourceUpperBranchingEnd t s) :
    let d := upperTerminalDepth (sourceUpperLogRadius t)
    let r := upperTerminalFineRadius (sourceUpperLogRadius t)
    let x := sourceUpperTarget t s
    let q := x - u
    let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
    sourceUpperTerminalWindowWeight t s C κ u *
      (sourceUpperBranchingSlack t s u * Real.exp (-u ^ 2 / (2 * L))) ≤
      (C * r ^ 2 * Real.exp (-2 * d) * Real.exp (2 + κ)) *
        ((S + q) / d * (1 + max q 0 / Real.sqrt d) *
          Real.exp (-(x - q) ^ 2 / (2 * L) - 2 * q - (κ / 2) * (max q 0) ^ 2 / d)) := by
  dsimp only
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let q := x - u
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  let W := C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d)
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hslack : 0 ≤ sourceUpperBranchingSlack t s u := by
    unfold sourceUpperBranchingSlack
    linarith
  have hS : sourceUpperBranchingSlack t s u ≤ S + q := by
    dsimp [sourceUpperBranchingSlack, sourceUpperBranchingEnd, S, q, x, d]
    linarith
  have hxq : x - q = u := by dsimp [q]; ring
  have hs := positive_gaussian_unit_shift_bound q κ d hκ hd
  have he : Real.exp (-(x - q) ^ 2 / (2 * L) - 2 * q -
      (κ / 2) * (max q 0) ^ 2 / d) =
      Real.exp (-u ^ 2 / (2 * L)) *
        Real.exp (-2 * q - (κ / 2) * (max q 0) ^ 2 / d) := by
    rw [hxq, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (W * sourceUpperBranchingSlack t s u * Real.exp (-u ^ 2 / (2 * L))) *
        Real.exp (-2 * q + 2 - κ * (max (q - 1) 0) ^ 2 / d) := by
      dsimp [W, sourceUpperTerminalWindowWeight, d, r, q, x]
      ring
    _ ≤ (W * sourceUpperBranchingSlack t s u * Real.exp (-u ^ 2 / (2 * L))) *
        (Real.exp (2 + κ) * Real.exp (-2 * q - (κ / 2) * (max q 0) ^ 2 / d)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (W * (S + q) * Real.exp (-u ^ 2 / (2 * L))) *
        (Real.exp (2 + κ) * Real.exp (-2 * q - (κ / 2) * (max q 0) ^ 2 / d)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hW) (by positivity)
    _ = _ := by
      rw [he]
      dsimp [W, d, r, S, q, x]
      ring

end SRWTightness
