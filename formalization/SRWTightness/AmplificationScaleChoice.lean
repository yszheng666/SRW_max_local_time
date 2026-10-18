import SRWTightness.CenteringAlgebra
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

noncomputable def amplificationScale (s : ℝ) : ℕ := ⌊Real.exp (s * Real.sqrt Real.pi / 4)⌋₊

theorem amplificationScale_pos (s : ℝ) (hs : 0 ≤ s) : 1 ≤ amplificationScale s := by
  unfold amplificationScale
  apply (Nat.one_le_floor_iff _).mpr
  apply Real.one_le_exp
  positivity

theorem diskCenter_amplification_shift (s R : ℝ) (hs : 0 ≤ s) (hR : (amplificationScale s : ℝ) < R) :
    diskCenter R - diskCenter (R / amplificationScale s) ≤ s / 2 := by
  have hQ : (1 : ℝ) ≤ amplificationScale s := by exact_mod_cast amplificationScale_pos s hs
  have hQ0 : (0 : ℝ) < amplificationScale s := by linarith
  have hlog : Real.log (amplificationScale s : ℝ) ≤ s * Real.sqrt Real.pi / 4 := by
    calc
      _ ≤ Real.log (Real.exp (s * Real.sqrt Real.pi / 4)) :=
        Real.log_le_log hQ0 (Nat.floor_le (Real.exp_pos _).le)
      _ = _ := Real.log_exp _
  refine (diskCenter_quotient_difference_le R (amplificationScale s) hQ hR).trans ?_
  have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / Real.sqrt Real.pi)
  have he : (2 / Real.sqrt Real.pi) * (s * Real.sqrt Real.pi / 4) = s / 2 := by
    have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp <;> ring
  rwa [he] at h

theorem amplificationScale_geometry (s R : ℝ) (hs : 0 ≤ s) (hR : (amplificationScale s : ℝ) < R) :
    (amplificationScale s / 2 : ℕ) * (R / amplificationScale s + 1) < R := by
  have hQ : (1 : ℝ) ≤ amplificationScale s := by exact_mod_cast amplificationScale_pos s hs
  have hQ0 : (0 : ℝ) < amplificationScale s := by linarith
  have hJ : (2 : ℝ) * (amplificationScale s / 2 : ℕ) ≤ amplificationScale s := by
    exact_mod_cast (show 2 * (amplificationScale s / 2) ≤ amplificationScale s by omega)
  have hR0 : 0 < R := by linarith
  have hA : 0 ≤ R / amplificationScale s + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right (show ((amplificationScale s / 2 : ℕ) : ℝ) ≤
      (amplificationScale s : ℝ) / 2 by linarith) hA
  have he : ((amplificationScale s : ℝ) / 2) * (R / amplificationScale s + 1) =
      (R + amplificationScale s) / 2 := by field_simp
  rw [he] at hmul
  linarith

end SRWTightness
