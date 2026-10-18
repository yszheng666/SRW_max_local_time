import SRWTightness.GaussianCoordinateIncrementTail
import SRWTightness.PlanarDyadicChain

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace SRWTightness

/-- Each actual Gaussian dyadic-chain increment has the claimed normalized closed tail. -/
theorem planar_gaussian_chain_increment_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (J : Finset ι) (o : ι) (ho : o ∈ J)
    (p : ι → ℝ × ℝ) (L K r : ℝ) (hL : 0 < L) (hK : 0 < K) (hr : 0 < r)
    (hp : ∀ x ∈ J, (p x).1 ^ 2 + (p x).2 ^ 2 ≤ (K * r) ^ 2)
    (hvar : ∀ x ∈ J, ∀ y ∈ J, S x x + S y y - 2 * S x y ≤
      L * (((p x).1 - (p y).1) ^ 2 + ((p x).2 - (p y).2) ^ 2) / r ^ 2)
    (n : ℕ) (x : ι) (hx : x ∈ J) (u : ℝ) (hu : 0 ≤ u) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
      {φ | Real.sqrt (32 * L * K ^ 2) * (u + n + 1) / 2 ^ n ≤
        |φ (planarDyadicChain J p o (K * r) (n + 1) x) -
          φ (planarDyadicChain J p o (K * r) n x)|} ≤
      2 * Real.exp (-((u + n + 1) ^ 2) / 2) := by
  let a := planarDyadicChain J p o (K * r) (n + 1) x
  let b := planarDyadicChain J p o (K * r) n x
  let V := 32 * L * K ^ 2
  have hV : 0 < V := by dsimp [V]; positivity
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hv : S a a + S b b - 2 * S a b ≤ V / ((2 : ℝ) ^ n) ^ 2 := by
    have hh := hvar a (planarDyadicChain_mem J p o ho _ _ x hx)
      b (planarDyadicChain_mem J p o ho _ _ x hx)
    have hg := planarDyadicChain_increment_bound J p o ho (K * r) (mul_pos hK hr) hp n x hx
    have ht := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hL.le) (sq_nonneg r)
    apply hh.trans
    convert ht using 1
    dsimp [V]
    field_simp
  have hsub := gaussian_coordinate_increment_subgaussian S hS a b
    (V / ((2 : ℝ) ^ n) ^ 2).toNNReal (by
      rw [Real.coe_toNNReal _ (by positivity)]
      exact hv)
  have ht := subgaussian_closed_absolute_tail _ _ _ hsub
    (Real.sqrt V * (u + n + 1) / 2 ^ n) (by positivity)
  rw [Real.coe_toNNReal _ (by positivity)] at ht
  have he : -(Real.sqrt V * (u + n + 1) / 2 ^ n) ^ 2 /
      (2 * (V / ((2 : ℝ) ^ n) ^ 2)) = -((u + n + 1) ^ 2) / 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hV.le]
    field_simp
  exact he ▸ ht

/-- The whole finite edge set at one scale has a uniform tail independent of observation count. -/
theorem planar_gaussian_chain_level_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (J : Finset ι) (o : ι) (ho : o ∈ J)
    (p : ι → ℝ × ℝ) (L K r : ℝ) (hL : 0 < L) (hK : 0 < K) (hr : 0 < r)
    (hp : ∀ x ∈ J, (p x).1 ^ 2 + (p x).2 ^ 2 ≤ (K * r) ^ 2)
    (hvar : ∀ x ∈ J, ∀ y ∈ J, S x x + S y y - 2 * S x y ≤
      L * (((p x).1 - (p y).1) ^ 2 + ((p x).2 - (p y).2) ^ 2) / r ^ 2)
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
      {φ | ∃ x ∈ J, Real.sqrt (32 * L * K ^ 2) * (u + n + 1) / 2 ^ n ≤
        |φ (planarDyadicChain J p o (K * r) (n + 1) x) -
          φ (planarDyadicChain J p o (K * r) n x)|} ≤
      162 * (16 : ℝ) ^ n * Real.exp (-((u + n + 1) ^ 2) / 2) := by
  let E := J.image (fun x ↦ (planarDyadicChain J p o (K * r) (n + 1) x,
    planarDyadicChain J p o (K * r) n x))
  let θ := Real.sqrt (32 * L * K ^ 2) * (u + n + 1) / 2 ^ n
  have he : {φ : EuclideanSpace ℝ ι | ∃ x ∈ J, θ ≤
      |φ (planarDyadicChain J p o (K * r) (n + 1) x) -
        φ (planarDyadicChain J p o (K * r) n x)|} =
      ⋃ e ∈ E, {φ : EuclideanSpace ℝ ι | θ ≤ |φ e.1 - φ e.2|} := by
    ext φ
    simp [E]
  change (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real _ ≤ _
  rw [he]
  have htail (e : ι × ι) (he : e ∈ E) :
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real {φ | θ ≤ |φ e.1 - φ e.2|} ≤
        2 * Real.exp (-((u + n + 1) ^ 2) / 2) := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact planar_gaussian_chain_increment_tail S hS J o ho p L K r hL hK hr hp hvar n x hx u hu
  have hh := (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum htail)
  have hc : (E.card : ℝ) ≤ 81 * (16 : ℝ) ^ n := by
    exact_mod_cast planarDyadicChain_edge_card J p o (K * r) (mul_pos hK hr) hp n
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  nlinarith [mul_le_mul_of_nonneg_right hc
    (Real.exp_nonneg (-((u + n + 1) ^ 2) / 2))]

end SRWTightness
