import SRWTightness.ExternalGaussianEndpointResidual
import SRWTightness.PairEndpointShift
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace

namespace SRWTightness

/-- Rebuild the average coordinates and two sites from independent averages and residuals. -/
noncomputable def pairGaussianRebuildLinear {n : ℕ} (last : Fin n) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ]
      EuclideanSpace ℝ (PairObservationIndex n) where
  toFun p := toLp 2 (fun j ↦ match j with
    | Sum.inl a => p.1 a
    | Sum.inr c => p.1 last + p.2 (if c then 1 else 0))
  map_add' p q := by
    ext j
    cases j <;> simp <;> ring
  map_smul' c p := by
    ext j
    cases j <;> simp [smul_eq_mul] <;> ring

/-- The endpoint-residual reconstruction is continuous and linear. -/
noncomputable def pairGaussianRebuildCLM {n : ℕ} (last : Fin n) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 2)) →L[ℝ]
      EuclideanSpace ℝ (PairObservationIndex n) :=
  (pairGaussianRebuildLinear last).toContinuousLinearMap

/-- The average dual vector absorbs both site coefficients at the final average. -/
theorem pair_gaussian_rebuild_dual_inl {n : ℕ} (last : Fin n)
    (u : EuclideanSpace ℝ (PairObservationIndex n)) :
    ((InnerProductSpace.toDualMap ℝ _ u).comp (pairGaussianRebuildCLM last)).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 2))) =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin n))
        (toLp 2 (pairEndpointShift last (fun j ↦ u (.inl j))
          (u (.inr false)) (u (.inr true)))) := by
  ext v
  simp [pairGaussianRebuildCLM, pairGaussianRebuildLinear,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_bool, pairEndpointShift, add_mul, mul_add, ite_mul, mul_ite,
    Finset.sum_add_distrib] <;> ring

/-- The residual dual vector consists of exactly the two site coefficients. -/
theorem pair_gaussian_rebuild_dual_inr {n : ℕ} (last : Fin n)
    (u : EuclideanSpace ℝ (PairObservationIndex n)) :
    ((InnerProductSpace.toDualMap ℝ _ u).comp (pairGaussianRebuildCLM last)).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 2))) =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin 2))
        (toLp 2 ![u (.inr false), u (.inr true)]) := by
  ext v
  simp [pairGaussianRebuildCLM, pairGaussianRebuildLinear,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_bool, Fin.sum_univ_two] <;> ring

end SRWTightness
