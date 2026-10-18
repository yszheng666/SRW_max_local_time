import SRWTightness.GaussianCoordinateMoments
import SRWTightness.ObservationMeshInterpolation
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual finite Gaussian coordinate law is jointly Gaussian. -/
theorem gaussianCoordinateLaw_joint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) : HasGaussianLaw (fun x : ι → ℝ ↦ x) (gaussianCoordinateLaw K) where
  isGaussian_map := by
    change IsGaussian ((gaussianCoordinateLaw K).map id)
    rw [Measure.map_id]
    let L : EuclideanSpace ℝ ι →L[ℝ] (ι → ℝ) :=
      { toFun x i := x i
        map_add' x y := by ext i; rfl
        map_smul' c x := by ext i; rfl }
    have h : HasGaussianLaw (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
        (multivariateGaussian 0 K) := IsGaussian.hasGaussianLaw_id
    exact (h.map L).isGaussian_map

/-- Insert the deterministic zero initial node and retain just the average coordinates. -/
theorem observationMeshValue_gaussian (n : ℕ) (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    HasGaussianLaw (fun x (j : Fin (n + 1)) ↦ observationMeshValue x j)
      (gaussianCoordinateLaw K) := by
  let L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    { toFun x j := observationMeshValue x j
      map_add' x y := by
        ext j
        by_cases h : 0 < j.val ∧ j.val ≤ n
        · simp only [observationMeshValue, dif_pos h, Pi.add_apply]
        · simp only [observationMeshValue, dif_neg h, Pi.add_apply, add_zero]
      map_smul' c x := by
        ext j
        by_cases h : 0 < j.val ∧ j.val ≤ n
        · simp only [observationMeshValue, dif_pos h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        · simp only [observationMeshValue, dif_neg h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_zero]
      cont := continuous_pi fun j ↦ by
        unfold observationMeshValue
        split
        · exact continuous_apply _
        · exact continuous_const }
  exact (gaussianCoordinateLaw_joint K).map L

theorem observationMeshValue_measurable (n j : ℕ) :
    Measurable (fun x : Fin (n + 1) → ℝ ↦ observationMeshValue x j) := by
  unfold observationMeshValue
  split
  · exact measurable_pi_apply _
  · exact measurable_const

theorem observationMeshValue_mean (n j : ℕ) (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (∫ x, observationMeshValue x j ∂gaussianCoordinateLaw K) = 0 := by
  unfold observationMeshValue
  split
  · exact gaussianCoordinateLaw_mean K _
  · simp

theorem observationMeshValue_memLp (n j : ℕ) (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    MemLp (fun x ↦ observationMeshValue x j) 2 (gaussianCoordinateLaw K) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  unfold observationMeshValue
  split
  · exact gaussianCoordinateLaw_coordinate_memLp_two K _
  · exact memLp_const 0

theorem observationMeshValue_covariance_succ (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hK : K.PosSemidef) (i j : Fin n) :
    cov[fun x ↦ observationMeshValue x (i.val + 1),
      fun x ↦ observationMeshValue x (j.val + 1); gaussianCoordinateLaw K] =
        K i.castSucc j.castSucc := by
  simp_rw [observationMeshValue_succ]
  exact gaussianCoordinateLaw_covariance K hK _ _

end SRWTightness
