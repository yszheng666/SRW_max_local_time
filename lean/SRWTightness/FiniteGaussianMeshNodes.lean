import SRWTightness.GaussianObservationNodes
import SRWTightness.FiniteGaussianPrefixMeasurable

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Insert the deterministic zero initial node and retain just the average coordinates. -/
theorem finiteGaussianMesh_gaussian (n M : ℕ) (K : Matrix (Fin n) (Fin n) ℝ) :
    HasGaussianLaw (fun x (j : Fin (M + 1)) ↦ finiteGaussianMesh n x j)
      (gaussianCoordinateLaw K) := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin (M + 1) → ℝ) :=
    { toFun x j := finiteGaussianMesh n x j
      map_add' x y := by
        ext j
        by_cases h : 0 < j.val ∧ j.val ≤ n
        · simp only [finiteGaussianMesh, dif_pos h, Pi.add_apply]
        · simp only [finiteGaussianMesh, dif_neg h, Pi.add_apply, add_zero]
      map_smul' c x := by
        ext j
        by_cases h : 0 < j.val ∧ j.val ≤ n
        · simp only [finiteGaussianMesh, dif_pos h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        · simp only [finiteGaussianMesh, dif_neg h, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply, mul_zero]
      cont := continuous_pi fun j ↦ by
        unfold finiteGaussianMesh
        split
        · exact continuous_apply _
        · exact continuous_const }
  exact (gaussianCoordinateLaw_joint K).map L

theorem finiteGaussianMesh_mean (n j : ℕ) (K : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, finiteGaussianMesh n x j ∂gaussianCoordinateLaw K) = 0 := by
  unfold finiteGaussianMesh
  split
  · exact gaussianCoordinateLaw_mean K _
  · simp

theorem finiteGaussianMesh_memLp (n j : ℕ) (K : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x ↦ finiteGaussianMesh n x j) 2 (gaussianCoordinateLaw K) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  unfold finiteGaussianMesh
  split
  · exact gaussianCoordinateLaw_coordinate_memLp_two K _
  · exact memLp_const 0


end SRWTightness
