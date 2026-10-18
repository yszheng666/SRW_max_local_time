import SRWTightness.SourceUpperBarrierAlgebra
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace SRWTightness

/-- The source spatial barrier algebra combines local tails, mesh weights, and the slope factor.
The local and mesh inequalities are explicit premises; no SRW mesh estimate is assumed globally. -/
theorem upper_barrier_spatial_sum {ι : Type*} (Z : Finset ι) (p ψ : ι → ℝ)
    (θ j U K C₁ C₂ C₃ : ℝ) (hj : 0 ≤ j) (hK : 0 ≤ K) (hden : 0 < j + K)
    (hθ : 3 / 2 ≤ θ) (hθthree : θ ≤ 3) (hU : 0 ≤ U)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hlocal : ∀ z ∈ Z, p z ≤ C₁ * ψ z / (j + 1) *
      Real.exp (-(θ * j + U) ^ 2 / (2 * (j + K))))
    (hmesh : (∑ z ∈ Z, ψ z) ≤ C₂ * (j + 1) ^ 2 * Real.exp (2 * j))
    (hslope : Real.exp ((2 - θ ^ 2 / 2) * j) ≤ C₃ * (j + 1) ^ 2) :
    (∑ z ∈ Z, p z) ≤ (C₁ * C₂ * C₃ * Real.exp (9 * K / 2)) *
      (j + 1) ^ 3 * Real.exp (-3 * U / 2) := by
  let V := (θ * j + U) ^ 2 / (2 * (j + K))
  have hJ : 0 < j + 1 := by linarith
  have hlocal' : ∀ z ∈ Z, p z ≤ (C₁ / (j + 1) * Real.exp (-V)) * ψ z := by
    intro z hz
    have h := hlocal z hz
    calc
      _ ≤ _ := h
      _ = _ := by simp only [V, neg_div]; ring
  have hsum : (∑ z ∈ Z, p z) ≤
      (C₁ / (j + 1) * Real.exp (-V)) * (∑ z ∈ Z, ψ z) := by
    simpa only [Finset.mul_sum] using Finset.sum_le_sum hlocal'
  have hcoef : 0 ≤ C₁ / (j + 1) * Real.exp (-V) := by positivity
  have hbase : (∑ z ∈ Z, p z) ≤
      C₁ * C₂ * (j + 1) * Real.exp (2 * j - V) := by
    calc
      _ ≤ (C₁ / (j + 1) * Real.exp (-V)) *
          (C₂ * (j + 1) ^ 2 * Real.exp (2 * j)) :=
        hsum.trans (mul_le_mul_of_nonneg_left hmesh hcoef)
      _ = _ := by
        rw [show 2 * j - V = -V + 2 * j by ring, Real.exp_add]
        field_simp
  have hexp := source_upper_barrier_exponential θ j U K hden hθ hθthree hU hK
  change Real.exp (2 * j - V) ≤ Real.exp (9 * K / 2) *
    Real.exp ((2 - θ ^ 2 / 2) * j) * Real.exp (-3 * U / 2) at hexp
  have hnonneg : 0 ≤ C₁ * C₂ * (j + 1) := by positivity
  have hreplace := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hslope (Real.exp_pos (9 * K / 2)).le)
      (Real.exp_pos (-3 * U / 2)).le) hnonneg
  calc
    _ ≤ C₁ * C₂ * (j + 1) * Real.exp (2 * j - V) := hbase
    _ ≤ C₁ * C₂ * (j + 1) * (Real.exp (9 * K / 2) *
        Real.exp ((2 - θ ^ 2 / 2) * j) * Real.exp (-3 * U / 2)) :=
      mul_le_mul_of_nonneg_left hexp hnonneg
    _ ≤ C₁ * C₂ * (j + 1) * (Real.exp (9 * K / 2) *
        (C₃ * (j + 1) ^ 2) * Real.exp (-3 * U / 2)) := hreplace
    _ = _ := by ring

end SRWTightness
