import SRWTightness.BrownianTimeCovariance

open Matrix

namespace SRWTightness

theorem matrix_quadratic_reindex {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ)
    (e : ι ≃ ι) (x : ι → ℝ) :
    x ⬝ᵥ (K.submatrix e e *ᵥ x) =
      (x ∘ e.symm) ⬝ᵥ (K *ᵥ (x ∘ e.symm)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]

theorem matrix_quadratic_lower_reindex {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℝ) (e : ι ≃ ι) (c : ℝ)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x)) (x : ι → ℝ) :
    c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K.submatrix e e *ᵥ x) := by
  rw [matrix_quadratic_reindex]
  have hh := hlo (x ∘ e.symm)
  have hs : (∑ i, (x ∘ e.symm) i ^ 2) = ∑ i, x i ^ 2 :=
    e.symm.sum_comp (fun i ↦ x i ^ 2)
  rwa [hs] at hh

end SRWTightness
