import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology
namespace SRWTightness

/-- The finite odd harmonic sum is the difference of two ordinary harmonic numbers. -/
theorem odd_harmonic_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1)) =
      (harmonic (2 * n) : ℝ) - (1 / 2 : ℝ) * (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    push_cast
    have he : 1 / (2 * (n : ℝ) + 1 + 1) = (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1)) := by
      field_simp
      <;> ring
    simp only [← one_div] at *
    rw [he]
    ring

/-- The odd harmonic sum has its exact Euler--Mascheroni logarithmic constant. -/
theorem odd_harmonic_sum_limit :
    Tendsto (fun n : ℕ ↦ (∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1)) -
      (1 / 2 : ℝ) * Real.log n) atTop
      (𝓝 (Real.eulerMascheroniConstant / 2 + Real.log 2)) := by
  have h2 : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by change n ≤ 2 * n; omega) tendsto_id
  have hlim := ((Real.tendsto_harmonic_sub_log.comp h2).sub
    ((tendsto_const_nhds (x := (1 / 2 : ℝ))).mul Real.tendsto_harmonic_sub_log)).add
      (tendsto_const_nhds (x := Real.log 2))
  have htarget : Real.eulerMascheroniConstant - (1 / 2 : ℝ) *
      Real.eulerMascheroniConstant + Real.log 2 =
      Real.eulerMascheroniConstant / 2 + Real.log 2 := by ring
  rw [htarget] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat]
  rw [odd_harmonic_sum, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0]
  ring

end SRWTightness
