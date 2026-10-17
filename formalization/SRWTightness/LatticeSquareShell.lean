import SRWTightness.LatticeNorm
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Integer square used to count the actual two-dimensional lattice shells. -/
noncomputable def centeredLatticeSquare (n : ℕ) : Finset Site :=
  (Finset.Icc (-(n : ℤ)) n).product (Finset.Icc (-(n : ℤ)) n)

theorem centeredLatticeSquare_zero : centeredLatticeSquare 0 = {0} := by
  simp [centeredLatticeSquare]

theorem centeredLatticeSquare_mono {n m : ℕ} (hnm : n ≤ m) :
    centeredLatticeSquare n ⊆ centeredLatticeSquare m := by
  have h : (n : ℤ) ≤ m := by exact_mod_cast hnm
  exact Finset.product_subset_product (Finset.Icc_subset_Icc (neg_le_neg h) h)
    (Finset.Icc_subset_Icc (neg_le_neg h) h)

/-- The exact square cardinality, in real coordinates for summation estimates. -/
theorem centeredLatticeSquare_card (n : ℕ) :
    ((centeredLatticeSquare n).card : ℝ) = (2 * (n : ℝ) + 1) ^ 2 := by
  have hc : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [centeredLatticeSquare, Finset.product_eq_sprod, Finset.card_product, hc]
  push_cast
  ring

/-- A square shell of integer radius n+1 has exactly eight times that radius many points. -/
theorem centeredLatticeSquare_shell_card (n : ℕ) :
    ((centeredLatticeSquare (n + 1) \ centeredLatticeSquare n).card : ℝ) = 8 * ((n : ℝ) + 1) := by
  have hs := centeredLatticeSquare_mono (Nat.le_succ n)
  rw [Finset.card_sdiff_of_subset hs, Nat.cast_sub (Finset.card_le_card hs),
    centeredLatticeSquare_card, centeredLatticeSquare_card]
  push_cast
  ring

/-- Outside the integer square, the Euclidean radius is at least the next integer. -/
theorem normSq_lower_outside_centeredLatticeSquare (n : ℕ) (z : Site)
    (hz : z ∉ centeredLatticeSquare n) :
    ((n : ℝ) + 1) ^ 2 ≤ normSq z := by
  by_contra h
  have hs : normSq z < ((n : ℝ) + 1) ^ 2 := lt_of_not_ge h
  have bound (u v : ℤ) (huv : (u : ℝ) ^ 2 + (v : ℝ) ^ 2 < ((n : ℝ) + 1) ^ 2) :
      -(n : ℤ) ≤ u ∧ u ≤ (n : ℤ) := by
    constructor
    · by_contra hlow
      have hi : u ≤ -(n : ℤ) - 1 := by omega
      have hr : (u : ℝ) ≤ -(n : ℝ) - 1 := by exact_mod_cast hi
      nlinarith [sq_nonneg (v : ℝ), Nat.cast_nonneg (α := ℝ) n]
    · by_contra hhigh
      have hi : (n : ℤ) + 1 ≤ u := by omega
      have hr : (n : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast hi
      nlinarith [sq_nonneg (v : ℝ), Nat.cast_nonneg (α := ℝ) n]
  apply hz
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr (bound z.1 z.2 hs),
      Finset.mem_Icc.mpr (bound z.2 z.1 (by simpa only [normSq, add_comm] using hs))⟩

/-- Inverse-radius bounds sum linearly over the exact integer square shells. -/
theorem centeredLatticeSquare_sum_bound (f : Site → ℝ) (A : ℝ) (hzero : f 0 ≤ A)
    (hshell : ∀ n : ℕ, ∀ z ∈ centeredLatticeSquare (n + 1) \ centeredLatticeSquare n,
      f z ≤ A / ((n : ℝ) + 1)) (N : ℕ) :
    (∑ z ∈ centeredLatticeSquare N, f z) ≤ A * (1 + 8 * (N : ℝ)) := by
  induction N with
  | zero => simpa only [centeredLatticeSquare_zero, Finset.sum_singleton, Nat.cast_zero,
      mul_zero, add_zero, mul_one] using hzero
  | succ n ih =>
    have hsub := centeredLatticeSquare_mono (Nat.le_succ n)
    have hs : (∑ z ∈ centeredLatticeSquare (n + 1) \ centeredLatticeSquare n, f z) ≤ 8 * A := by
      calc
        _ ≤ ∑ z ∈ centeredLatticeSquare (n + 1) \ centeredLatticeSquare n, A / ((n : ℝ) + 1) :=
          Finset.sum_le_sum (hshell n)
        _ = 8 * A := by
          rw [Finset.sum_const, nsmul_eq_mul, centeredLatticeSquare_shell_card]
          field_simp
    rw [← Finset.sum_sdiff hsub]
    push_cast
    linarith

end SRWTightness
