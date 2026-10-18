import SRWTightness.UpperTerminalQuadraticFactor
import SRWTightness.SourceUpperTerminalWindowProbability

namespace SRWTightness

/-- The actual window weight times the branching Gaussian is dominated by the normalized tilt sum. -/
theorem source_upper_terminal_window_product (t s C κ u L : ℝ)
    (hC : 0 ≤ C) (hL : 0 < L)
    (hd : 0 < upperTerminalDepth (sourceUpperLogRadius t))
    (hu : u ≤ sourceUpperBranchingEnd t s) :
    let d := upperTerminalDepth (sourceUpperLogRadius t)
    let r := upperTerminalFineRadius (sourceUpperLogRadius t)
    let x := sourceUpperTarget t s
    let q := x - u
    let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
    sourceUpperTerminalWindowWeight t s C κ u *
      (sourceUpperBranchingSlack t s u * Real.exp (-u ^ 2 / (2 * L))) ≤
      (C * r ^ 2 * Real.exp (-2 * d) * Real.exp 2 * Real.exp (-x ^ 2 / (2 * L))) *
        ((S + q) * (1 + max q 0 / Real.sqrt d) / d *
          Real.exp ((x / L - 2) * q - κ * (max (q - 1) 0) ^ 2 / d)) := by
  dsimp only
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let q := x - u
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  let z := κ * (max (q - 1) 0) ^ 2 / d
  let W := C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hslack : 0 ≤ sourceUpperBranchingSlack t s u := by
    unfold sourceUpperBranchingSlack
    linarith
  have hslackS : sourceUpperBranchingSlack t s u ≤ S + q := by
    dsimp [sourceUpperBranchingSlack, sourceUpperBranchingEnd, S, q, x, d]
    linarith
  have hxq : x - q = u := by dsimp [q]; ring
  have he := upper_terminal_quadratic_factor L x q (2 - z) hL
  rw [hxq] at he
  have heq : Real.exp (-u ^ 2 / (2 * L) - 2 * q + (2 - z)) =
      Real.exp (-2 * q + 2 - z) * Real.exp (-u ^ 2 / (2 * L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htilt : Real.exp ((x / L - 2) * q + (2 - z)) =
      Real.exp 2 * Real.exp ((x / L - 2) * q - z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (W * sourceUpperBranchingSlack t s u) *
        Real.exp (-u ^ 2 / (2 * L) - 2 * q + (2 - z)) := by
      rw [heq]
      dsimp [W, z, q, x, r, d, sourceUpperTerminalWindowWeight]
      ring
    _ ≤ (W * sourceUpperBranchingSlack t s u) *
        (Real.exp (-x ^ 2 / (2 * L)) * Real.exp ((x / L - 2) * q + (2 - z))) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hW hslack)
    _ ≤ (W * (S + q)) *
        (Real.exp (-x ^ 2 / (2 * L)) * Real.exp ((x / L - 2) * q + (2 - z))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hslackS hW) (by positivity)
    _ = _ := by
      rw [htilt]
      dsimp [W, z, q, x, S, r, d]
      ring

end SRWTightness
