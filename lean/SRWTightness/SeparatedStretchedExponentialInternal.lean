import SRWTightness.StretchedExponentialPolynomial
import Mathlib.Analysis.PSeries

open scoped BigOperators

namespace SRWTightness

/-- The stretched-exponential mesh kernel is bounded by an inverse square on the positive line. -/
theorem stretched_exponential_kernel_inverse_square (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      ((1 + x ^ γ) / x) * Real.exp (-c * x ^ γ) ≤ C / x ^ 2 := by
  obtain ⟨C₁, hC₁, hb₁⟩ := stretched_exponential_polynomial_bound 1 c γ zero_lt_one hc hγ
  obtain ⟨C₂, hC₂, hb₂⟩ := stretched_exponential_polynomial_bound (γ + 1) c γ
    (by linarith) hc hγ
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro x hx
  apply (le_div_iff₀ (sq_pos_of_pos hx)).mpr
  have he : (((1 + x ^ γ) / x) * Real.exp (-c * x ^ γ)) * x ^ 2 =
      x ^ (1 : ℝ) * Real.exp (-c * x ^ γ) +
        x ^ (γ + 1) * Real.exp (-c * x ^ γ) := by
    rw [Real.rpow_add hx, Real.rpow_one]
    field_simp <;> ring
  rw [he]
  exact add_le_add (hb₁ x hx.le) (hb₂ x hx.le)

/-- The original uniform separated-mesh summation input follows from the inverse-square series. -/
theorem separated_stretched_exponential_sum_input_internal :
    SeparatedStretchedExponentialSumInput := by
  intro δ h₀ c γ hδ hh₀ hc hγ
  obtain ⟨K, hK, hk⟩ := stretched_exponential_kernel_inverse_square c γ hc hγ
  let m := min δ h₀
  have hm : 0 < m := lt_min hδ hh₀
  let f : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ) + 1) ^ 2
  have hs : Summable f := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  let C := K / m ^ 2 * (∑' i, f i) + 1
  have hsum : 0 ≤ ∑' i, f i := tsum_nonneg (fun i ↦ by dsimp [f]; positivity)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N x hx hstep
  have hmesh : ∀ i ≤ N, m * ((i : ℝ) + 1) ≤ x i := by
    intro i hi
    induction i with
    | zero =>
      simpa only [Nat.cast_zero, zero_add, mul_one] using
        (min_le_right δ h₀).trans (hx 0 (Nat.zero_le N))
    | succ i ih =>
      have hprev := ih (by omega)
      have hgap := hstep i (by omega)
      have hmδ : m ≤ δ := min_le_left _ _
      push_cast
      linarith
  have hterm (i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
      ((1 + (x i) ^ γ) / x i) * Real.exp (-c * (x i) ^ γ) ≤ K / m ^ 2 * f i := by
    have hiN : i ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    have hxi : 0 < x i := hh₀.trans_le (hx i hiN)
    have hmip : 0 < m * ((i : ℝ) + 1) := by positivity
    calc
      _ ≤ K / (x i) ^ 2 := hk _ hxi
      _ ≤ K / (m * ((i : ℝ) + 1)) ^ 2 :=
        div_le_div_of_nonneg_left hK.le (sq_pos_of_pos hmip)
          (pow_le_pow_left₀ hmip.le (hmesh i hiN) 2)
      _ = K / m ^ 2 * f i := by dsimp [f]; field_simp <;> ring
  calc
    _ ≤ ∑ i ∈ Finset.range (N + 1), K / m ^ 2 * f i := Finset.sum_le_sum hterm
    _ = K / m ^ 2 * ∑ i ∈ Finset.range (N + 1), f i := (Finset.mul_sum _ _ _).symm
    _ ≤ K / m ^ 2 * (∑' i, f i) := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum _ (fun i _ ↦ by dsimp [f]; positivity)) (by positivity)
    _ ≤ C := by dsimp [C]; linarith

end SRWTightness
