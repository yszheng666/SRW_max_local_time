import SRWTightness.WhiteningMatrixBound

open Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- Uniform coordinate errors give the square-root dimension bound in Euclidean norm. -/
theorem euclidean_norm_le_coordinate_bound {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (ε : ℝ) (hε : 0 ≤ ε) (hx : ∀ i, |x i| ≤ ε) :
    ‖x‖ ≤ Real.sqrt (Fintype.card ι) * ε := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _ : ι, ε ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε).mpr (hx i)
    _ = _ := by simp

/-- A covariance gap controls the standardized norm of a coordinatewise mean error. -/
theorem whitened_mean_error_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (a : ℝ) (ha : 0 < a)
    (hlo : ∀ y : ι → ℝ, a * (∑ i, y i ^ 2) ≤ y ⬝ᵥ (G *ᵥ y))
    (x : EuclideanSpace ℝ ι) (ε : ℝ) (hε : 0 ≤ ε) (hx : ∀ i, |x i| ≤ ε) :
    ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt G)⁻¹) x‖ ≤
      Real.sqrt (Fintype.card ι) * ε / Real.sqrt a :=
  (matrix_whitening_norm_le G hG a ha hlo x).trans
    (div_le_div_of_nonneg_right (euclidean_norm_le_coordinate_bound x ε hε hx)
      (Real.sqrt_nonneg _))

/-- A vector energy contraction acts columnwise on the squared Frobenius norm. -/
theorem matrix_left_energy_bound {ι : Type*} [Fintype ι]
    (A E : Matrix ι ι ℝ) (a : ℝ)
    (hA : ∀ x : ι → ℝ, a * (∑ i, (A *ᵥ x) i ^ 2) ≤ ∑ i, x i ^ 2) :
    a * (∑ i, ∑ j, (A * E) i j ^ 2) ≤ ∑ i, ∑ j, E i j ^ 2 := by
  calc
    _ = a * (∑ j, ∑ i, (A * E) i j ^ 2) := by rw [Finset.sum_comm]
    _ = ∑ j, a * (∑ i, (A * E) i j ^ 2) := by rw [Finset.mul_sum]
    _ ≤ ∑ j, ∑ i, E i j ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply] using hA (fun i ↦ E i j)
    _ = _ := Finset.sum_comm

/-- Applying the same energy contraction on both sides controls the Frobenius error. -/
theorem matrix_sandwich_energy_bound {ι : Type*} [Fintype ι]
    (A E : Matrix ι ι ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hA : ∀ x : ι → ℝ, a * (∑ i, (A *ᵥ x) i ^ 2) ≤ ∑ i, x i ^ 2) :
    a ^ 2 * (∑ i, ∑ j, (A * E * Aᵀ) i j ^ 2) ≤ ∑ i, ∑ j, E i j ^ 2 := by
  have hleft := matrix_left_energy_bound A (E * Aᵀ) a hA
  have hright := matrix_left_energy_bound A Eᵀ a hA
  have he : A * Eᵀ = (E * Aᵀ)ᵀ := by simp
  rw [he] at hright
  simp only [Matrix.transpose_apply] at hright
  rw [Finset.sum_comm] at hright
  rw [Finset.sum_comm (f := fun i j ↦ E j i ^ 2)] at hright
  have hh := mul_le_mul_of_nonneg_left hleft ha
  rw [← Matrix.mul_assoc] at hh
  nlinarith

/-- Whitening a matrix perturbation retains its linear dimension Frobenius error bound. -/
theorem matrix_whitened_error_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G E : Matrix ι ι ℝ) (hG : G.PosDef) (a : ℝ) (ha : 0 < a)
    (hlo : ∀ y : ι → ℝ, a * (∑ i, y i ^ 2) ≤ y ⬝ᵥ (G *ᵥ y))
    (ε : ℝ) (hε : 0 ≤ ε) (hE : ∀ i j, |E i j| ≤ ε) :
    let A := (CFC.sqrt G)⁻¹
    ‖(toLp 2 (fun ij : ι × ι ↦ (A * E * Aᵀ) ij.1 ij.2) :
      EuclideanSpace ℝ (ι × ι))‖ ≤ Fintype.card ι * ε / a := by
  let A := (CFC.sqrt G)⁻¹
  have hA (x : ι → ℝ) : a * (∑ i, (A *ᵥ x) i ^ 2) ≤ ∑ i, x i ^ 2 := by
    have hh := hlo (A *ᵥ x)
    rw [matrix_whitening_energy G hG] at hh
    exact hh
  have hsum := matrix_sandwich_energy_bound A E a ha.le hA
  have he : (∑ i, ∑ j, E i j ^ 2) ≤ (Fintype.card ι : ℝ) ^ 2 * ε ^ 2 := by
    calc
      _ ≤ ∑ _ : ι, ∑ _ : ι, ε ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε).mpr (hE i j)
      _ = _ := by simp; ring
  apply (le_div_iff₀ ha).mpr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq]
  simp only [ofLp_toLp, Fintype.sum_prod_type]
  nlinarith

end SRWTightness
