import SRWTightness.BrownianTimeCovariance
import SRWTightness.SmallDiagonalResolvent

open Matrix

namespace SRWTightness

/-- The complete dimension-free inverse correction bound for Brownian observation times.
The diagonal error bound remains explicit and must be proved for an application. -/
theorem brownianTimeMatrix_inverse_correction (T : ℕ → ℝ) (hT : T 0 = 0) (n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ k < n, δ ≤ T (k + 1) - T k)
    (e : Fin n → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ δ / 8)
    (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (((brownianTimeMatrix T n - Matrix.diagonal e)⁻¹ -
      (brownianTimeMatrix T n)⁻¹) *ᵥ x) ∧
    x ⬝ᵥ (((brownianTimeMatrix T n - Matrix.diagonal e)⁻¹ -
      (brownianTimeMatrix T n)⁻¹) *ᵥ x) ≤
      2 * ∑ i, e i * ((brownianTimeMatrix T n)⁻¹ *ᵥ x) i ^ 2 := by
  let K := brownianTimeMatrix T n
  have hK : K.PosDef := by
    dsimp [K]
    rw [brownianTimeMatrix_eq_increment T hT n (fun k hk ↦ by linarith [hgap k hk])]
    exact incrementCovariance_posDef _ δ hδ (fun i ↦ hgap i.val i.isLt)
  have hlo (y : Fin n → ℝ) : (δ / 4) * (∑ i, y i ^ 2) ≤ y ⬝ᵥ (K *ᵥ y) := by
    have hh := brownianTimeMatrix_quadratic_lower T hT n δ hδ.le hgap y
    simpa only [K, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hh
  have hsmall : ∀ i, e i ≤ (δ / 4) / 2 := by
    intro i
    linarith [hesmall i]
  have hc : 0 < δ / 4 := div_pos hδ (by norm_num)
  have hJ := smallDiagonal_resolvent_posDef K hK (δ / 4) hc hlo e he hsmall
  have hJT := smallDiagonal_resolvent_lower K hK.isUnit (δ / 4) hc hlo e he hsmall
  have hKT : Kᵀ = K := by
    ext i j
    exact min_comm _ _
  exact covariance_diagonal_inverse_difference_bounds K e he hK.isUnit hKT hJ hJT x

end SRWTightness
