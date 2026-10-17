import SRWTightness.GaussianCovarianceSquareRoot

open Matrix WithLp

open scoped MatrixOrder

namespace SRWTightness

/-- The inverse square root sends the covariance quadratic form exactly to Euclidean energy. -/
theorem matrix_whitening_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (x : ι → ℝ) :
    ((CFC.sqrt G)⁻¹ *ᵥ x) ⬝ᵥ (G *ᵥ ((CFC.sqrt G)⁻¹ *ᵥ x)) = ∑ i, x i ^ 2 := by
  let S := CFC.sqrt G
  have hS : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt (matrix_sqrt_posDef G hG).det_pos)
  have he : S *ᵥ (S⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv S hS, one_mulVec]
  have hh := dotProduct_transpose_mulVec S (S⁻¹ *ᵥ x) (S *ᵥ (S⁻¹ *ᵥ x))
  rw [show Sᵀ = S from matrix_sqrt_symmetric G, mulVec_mulVec,
    show S * S = G from matrix_sqrt_square G hG.posSemidef, he] at hh
  simpa only [dotProduct, pow_two] using hh

/-- A lower covariance gap bounds the norm of its actual inverse-square-root map. -/
theorem matrix_whitening_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (a : ℝ) (ha : 0 < a)
    (hlo : ∀ y : ι → ℝ, a * (∑ i, y i ^ 2) ≤ y ⬝ᵥ (G *ᵥ y))
    (x : EuclideanSpace ℝ ι) :
    ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt G)⁻¹) x‖ ≤ ‖x‖ / Real.sqrt a := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hh := hlo ((CFC.sqrt G)⁻¹ *ᵥ ofLp x)
  rw [matrix_whitening_energy G hG] at hh
  have hn : a * ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt G)⁻¹) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, ofLp_toEuclideanCLM] using hh
  apply (le_div_iff₀ hs).mpr
  apply (sq_le_sq₀ (by positivity) (norm_nonneg x)).mp
  calc
    _ = a * ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt G)⁻¹) x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha.le]
      ring
    _ ≤ _ := hn

/-- The actual whitening matrix transforms its covariance matrix to the identity. -/
theorem matrix_whitening_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    (CFC.sqrt G)⁻¹ * G * ((CFC.sqrt G)⁻¹)ᵀ = 1 := by
  have hS : IsUnit (CFC.sqrt G).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (matrix_sqrt_posDef G hG).det_pos)
  calc
    _ = (CFC.sqrt G)⁻¹ * (CFC.sqrt G * CFC.sqrt G) * (CFC.sqrt G)⁻¹ := by
      rw [matrix_sqrt_square G hG.posSemidef, transpose_nonsing_inv, matrix_sqrt_symmetric]
    _ = 1 := by
      simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hS, one_mul, mul_nonsing_inv _ hS]

end SRWTightness
