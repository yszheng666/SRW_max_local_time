import SRWTightness.PlanarDyadicChainCover
import SRWTightness.GaussianCoordinateIncrementTail

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual Gaussian vector satisfies the dyadic event cover almost surely. -/
theorem planar_gaussian_chain_cover_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (J : Finset ι) (o : ι) (ho : o ∈ J)
    (h0 : S o o = 0) (p : ι → ℝ × ℝ) (L K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hvar : ∀ x ∈ J, ∀ y ∈ J, S x x + S y y - 2 * S x y ≤
      L * (((p x).1 - (p y).1) ^ 2 + ((p x).2 - (p y).2) ^ 2) / r ^ 2)
    (u : ℝ) (hu : 0 ≤ u) :
    ∀ᵐ φ : EuclideanSpace ℝ ι ∂multivariateGaussian 0 S,
      (∃ x ∈ J, Real.sqrt (32 * L * K ^ 2) * (2 * u + 4) ≤ |φ x|) →
      ∃ n : ℕ, ∃ x ∈ J, Real.sqrt (32 * L * K ^ 2) * (u + n + 1) / 2 ^ n ≤
        |φ (planarDyadicChain J p o (K * r) (n + 1) x) -
          φ (planarDyadicChain J p o (K * r) n x)| := by
  have heq : ∀ᵐ φ : EuclideanSpace ℝ ι ∂multivariateGaussian 0 S,
      ∀ i ∈ J, ∀ j ∈ J, p i = p j → φ i = φ j := by
    simp only [ae_all_iff]
    intro i hi j hj hij
    apply centered_multivariate_zero_increment S hS i j
    have hv := hvar i hi j hj
    simpa only [hij, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero,
      mul_zero, zero_div] using hv
  filter_upwards [centered_multivariate_zero_coordinate S hS o h0, heq] with φ hφ he
  exact planar_dyadic_chain_cover J p o ho (K * r) (mul_pos hK hr) φ hφ he
    _ u (Real.sqrt_nonneg _) hu

end SRWTightness
