import SRWTightness.FiniteGaussianMeshNodes
import SRWTightness.BrownianTimeCovariance

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Nondecreasing nonnegative mesh times give a positive semidefinite Brownian matrix. -/
theorem brownianTimeMatrix_posSemidef_of_gaps (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n, T j ≤ T (j + 1)) : (brownianTimeMatrix T n).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · ext i j
    simp [brownianTimeMatrix, min_comm]
  · intro x
    have hh := brownianTimeMatrix_quadratic_lower T hT n 0 le_rfl
      (fun j hj ↦ sub_nonneg.mpr (hgap j hj)) x
    simpa only [zero_div, zero_mul, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, star_trivial, Finset.sum_const_zero] using hh

theorem finiteGaussianMesh_zero (n : ℕ) (x : Fin n → ℝ) : finiteGaussianMesh n x 0 = 0 := by
  simp [finiteGaussianMesh]

theorem finiteGaussianMesh_succ (n : ℕ) (x : Fin n → ℝ) (j : Fin n) :
    finiteGaussianMesh n x (j.val + 1) = x j := by
  simp [finiteGaussianMesh, Nat.succ_le_of_lt j.isLt]

/-- All retained nodes have the exact Brownian covariance, including the zero initial node. -/
theorem finiteGaussianMesh_brownian_covariance (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n, T j < T (j + 1)) (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    cov[fun x ↦ finiteGaussianMesh n x i, fun x ↦ finiteGaussianMesh n x j;
      gaussianCoordinateLaw (brownianTimeMatrix T n)] = min (T i) (T j) := by
  let K := brownianTimeMatrix T n
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hK : K.PosSemidef := brownianTimeMatrix_posSemidef_of_gaps T n hT
    (fun j hj ↦ (hgap j hj).le)
  have hn (k : ℕ) (hk : k ≤ n) : 0 ≤ T k := by
    have hh := timeGridTime_mono T n hgap (Nat.zero_le k) hk
    simpa only [hT] using hh
  cases i with
  | zero =>
    simp only [finiteGaussianMesh_zero]
    rw [covariance_const_left, hT, min_eq_left (hn j hj)]
  | succ i =>
    cases j with
    | zero =>
      simp only [finiteGaussianMesh_zero]
      rw [covariance_const_right, hT, min_eq_right (hn (i + 1) hi)]
    | succ j =>
      have hsi (x : Fin n → ℝ) := finiteGaussianMesh_succ n x ⟨i, by omega⟩
      have hsj (x : Fin n → ℝ) := finiteGaussianMesh_succ n x ⟨j, by omega⟩
      simp_rw [hsi, hsj]
      exact gaussianCoordinateLaw_covariance K hK _ _

end SRWTightness
