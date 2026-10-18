import SRWTightness.ObservationCoefficientContraction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

noncomputable def pairTiltWeight {ι : Type*} [DecidableEq ι]
    (z y : ι) (w : ι → ℝ) (x : ι) : ℝ :=
  2 * (if x = z then 1 else 0) + 2 * (if x = y then 1 else 0) - 2 * w x

/-- The negative equilibrium coefficient still gives total absolute weight at most six. -/
theorem pairTiltWeight_l1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z y : ι) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) :
    (∑ x, |pairTiltWeight z y w x|) ≤ 6 := by
  have hp (x : ι) : |pairTiltWeight z y w x| ≤
      2 * (if x = z then 1 else 0) + 2 * (if x = y then 1 else 0) + 2 * w x := by
    unfold pairTiltWeight
    have h1 : 0 ≤ (2 : ℝ) * (if x = z then 1 else 0) := by positivity
    have h2 : 0 ≤ (2 : ℝ) * (if x = y then 1 else 0) := by positivity
    have h3 : 0 ≤ 2 * w x := mul_nonneg (by norm_num) (hw x)
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (add_nonneg h1 h2), abs_of_nonneg h3])
  calc
    _ ≤ ∑ x, (2 * (if x = z then 1 else 0) + 2 * (if x = y then 1 else 0) + 2 * w x) :=
      Finset.sum_le_sum (fun x _ ↦ hp x)
    _ = 6 := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw1] <;> norm_num

/-- Coordinate weights represent exactly the signed pair statistic. -/
theorem pairTiltWeight_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z y : ι) (w F : ι → ℝ) :
    (∑ x, pairTiltWeight z y w x * F x) = 2 * (F z + F y - ∑ x, w x * F x) := by
  simp only [pairTiltWeight, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end SRWTightness
