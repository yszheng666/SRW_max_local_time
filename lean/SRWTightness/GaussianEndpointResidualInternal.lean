import SRWTightness.PairGaussianResidualQuadratic
import SRWTightness.PairGaussianRebuildLinear
import SRWTightness.PairResidualProductLaw

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace

namespace SRWTightness

/-- Independent Gaussian averages and two residuals rebuild the compensated pair law. -/
theorem pair_gaussian_rebuild_law {n : ℕ} (last : Fin n)
    (T : Fin n → ℝ) (V : Matrix Bool Bool ℝ)
    (hmax : ∀ j, T j ≤ T last) (hV : V true false = V false true)
    (hB : Matrix.PosSemidef (fun j l : Fin n ↦ min (T j) (T l)))
    (hR : (pairResidualMatrix (V false false) (V true true) (V false true)
      (T last)).PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (fun j l ↦ min (T j) (T l))).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        (pairResidualMatrix (V false false) (V true true) (V false true) (T last)))).map
      (pairGaussianRebuildCLM last) =
      multivariateGaussian (0 : EuclideanSpace ℝ (PairObservationIndex n))
        (pairObservationCovarianceMatrix T (fun _ ↦ 0) V) := by
  have hquad (x : Fin n → ℝ) : 0 ≤ ∑ j, ∑ l, x j * min (T j) (T l) * x l := by
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, star_trivial] using
      hB.dotProduct_mulVec_nonneg x
  have hS := pair_gaussian_residual_posSemidef last T V hmax hV hquad hR
  apply Measure.ext_of_charFun
  ext u
  rw [charFun_eq_charFunDual_toDualMap, charFunDual_map, charFunDual_prod,
    pair_gaussian_rebuild_dual_inl, pair_gaussian_rebuild_dual_inr,
    ← charFun_eq_charFunDual_toDualMap, ← charFun_eq_charFunDual_toDualMap,
    charFun_multivariateGaussian hB, charFun_multivariateGaussian hR,
    charFun_multivariateGaussian hS]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← Complex.exp_add]
  congr 1
  let qB : ℝ := pairEndpointShift last (fun j ↦ u (.inl j))
    (u (.inr false)) (u (.inr true)) ⬝ᵥ ((fun j l ↦ min (T j) (T l)) *ᵥ
      pairEndpointShift last (fun j ↦ u (.inl j)) (u (.inr false)) (u (.inr true)))
  let qR : ℝ := (![u (.inr false), u (.inr true)] : Fin 2 → ℝ) ⬝ᵥ
    (pairResidualMatrix (V false false) (V true true) (V false true) (T last) *ᵥ
      ![u (.inr false), u (.inr true)])
  let qS : ℝ := u ⬝ᵥ (pairObservationCovarianceMatrix T (fun _ ↦ 0) V *ᵥ u)
  have hq : qB + qR = qS :=
    (pair_gaussian_residual_quadratic last T V hmax hV (ofLp u)).symm
  have hc : (qB : ℂ) + (qR : ℂ) = (qS : ℂ) := by exact_mod_cast hq
  change -((qB : ℂ) / 2) + -((qR : ℂ) / 2) = -((qS : ℂ) / 2)
  rw [← hc]
  ring

/-- The complete original Gaussian endpoint-residual input is internally proved. -/
theorem gaussian_endpoint_residual_input_internal : GaussianEndpointResidualInput := by
  intro n last T V hmax hV hquad hR
  have hB : Matrix.PosSemidef (fun j l : Fin n ↦ min (T j) (T l)) := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, ?_⟩
    · ext i j
      simp [min_comm]
    · intro x
      simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, star_trivial] using hquad x
  have hh := pair_gaussian_rebuild_law last T V hmax hV hB hR.posSemidef
  change gaussianCoordinateLaw (pairObservationCovarianceMatrix T (fun _ ↦ 0) V) =
    ((gaussianCoordinateLaw (fun j l ↦ min (T j) (T l))).prod
      (gaussianCoordinateLaw
        (pairResidualMatrix (V false false) (V true true) (V false true) (T last)))).map
      (pairResidualCoordinates last)
  unfold gaussianCoordinateLaw
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (pairResidualCoordinates_measurable last) (by fun_prop),
    ← hh, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

end SRWTightness
