import SRWTightness.PlanarGaussianChainCover
import SRWTightness.PlanarGaussianChainTail
import SRWTightness.DyadicGaussianTailSum
import SRWTightness.CountableCoverRealBound

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Summing the actual Gaussian chain proves a uniform shifted supremum tail. -/
theorem planar_gaussian_shifted_sup_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (J : Finset ι) (o : ι) (ho : o ∈ J)
    (h0 : S o o = 0) (p : ι → ℝ × ℝ) (L K r : ℝ) (hL : 0 < L) (hK : 0 < K) (hr : 0 < r)
    (hp : ∀ x ∈ J, (p x).1 ^ 2 + (p x).2 ^ 2 ≤ (K * r) ^ 2)
    (hvar : ∀ x ∈ J, ∀ y ∈ J, S x x + S y y - 2 * S x y ≤
      L * (((p x).1 - (p y).1) ^ 2 + ((p x).2 - (p y).2) ^ 2) / r ^ 2)
    (u : ℝ) (hu : 0 ≤ u) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
      {φ | ∃ x ∈ J, Real.sqrt (32 * L * K ^ 2) * (2 * u + 4) ≤ |φ x|} ≤
      (162 * ∑' n : ℕ, (16 : ℝ) ^ n * Real.exp (-((n : ℝ) + 1) ^ 2 / 2)) *
        Real.exp (-u ^ 2 / 2) := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) S
  let E : Set (EuclideanSpace ℝ ι) :=
    {φ | ∃ x ∈ J, Real.sqrt (32 * L * K ^ 2) * (2 * u + 4) ≤ |φ x|}
  let s := fun n : ℕ ↦ {φ : EuclideanSpace ℝ ι | ∃ x ∈ J,
    Real.sqrt (32 * L * K ^ 2) * (u + n + 1) / 2 ^ n ≤
      |φ (planarDyadicChain J p o (K * r) (n + 1) x) -
        φ (planarDyadicChain J p o (K * r) n x)|}
  have hcover : E ≤ᵐ[μ] ⋃ n, s n := by
    filter_upwards [planar_gaussian_chain_cover_ae S hS J o ho h0 p L K r hK hr hvar u hu]
      with φ hφ
    change (φ ∈ E) → φ ∈ ⋃ n, s n
    simpa only [E, s, Set.mem_setOf_eq, Set.mem_iUnion] using hφ
  have hm : μ.real E ≤ μ.real (⋃ n, s n) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hcover)
  have hh := countable_cover_real_bound μ (⋃ n, s n) s
    (fun n : ℕ ↦ 162 * (16 : ℝ) ^ n * Real.exp (-((u + n + 1) ^ 2) / 2))
    Set.Subset.rfl (fun n ↦ by positivity) (dyadic_gaussian_tail_sum_bound u hu).1
    (fun n ↦ planar_gaussian_chain_level_tail S hS J o ho p L K r hL hK hr hp hvar n u hu)
  exact hm.trans (hh.trans (dyadic_gaussian_tail_sum_bound u hu).2)

end SRWTightness
