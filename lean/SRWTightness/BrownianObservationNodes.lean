import SRWTightness.GaussianObservationNodes
import SRWTightness.BrownianTimeCovariance

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

theorem brownianTimeMatrix_posDef_of_unit_gaps (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n, 1 ≤ T (j + 1) - T j) : (brownianTimeMatrix T n).PosDef := by
  have hh := brownianTimeMatrix_sub_diagonal_posDef T hT n 1 (by norm_num) hgap
    (fun _ ↦ 0) (fun _ ↦ by norm_num)
  simpa using hh

theorem observationMeshValue_brownian_covariance (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    cov[fun x ↦ observationMeshValue x i, fun x ↦ observationMeshValue x j;
      gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))] = min (T i) (T j) := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hK : K.PosSemidef := (brownianTimeMatrix_posDef_of_unit_gaps T (n + 1) hT hgap).posSemidef
  have hn (k : ℕ) (hk : k ≤ n) : 0 ≤ T k := by
    have hh := timeGridTime_mono T (n + 1) (fun l hl ↦ by linarith [hgap l hl])
      (Nat.zero_le k) (by omega : k ≤ n + 1)
    simpa only [hT] using hh
  cases i with
  | zero =>
    simp only [observationMeshValue_zero]
    rw [covariance_const_left, hT, min_eq_left (hn j hj)]
  | succ i =>
    cases j with
    | zero =>
      simp only [observationMeshValue_zero]
      rw [covariance_const_right, hT, min_eq_right (hn (i + 1) hi)]
    | succ j =>
      have hh := observationMeshValue_covariance_succ n K hK ⟨i, by omega⟩ ⟨j, by omega⟩
      exact hh

end SRWTightness
