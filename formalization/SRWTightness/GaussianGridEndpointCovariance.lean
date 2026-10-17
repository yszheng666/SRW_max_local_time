import SRWTightness.GaussianGridPath

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

theorem observationMeshValue_site_covariance (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) (i : ℕ) (hi : i ≤ n) :
    cov[fun x ↦ observationMeshValue x i, fun x ↦ x (Fin.last n);
      gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))] = T i := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hK := (brownianTimeMatrix_posDef_of_unit_gaps T (n + 1) hT hgap).posSemidef
  cases i with
  | zero => simp only [observationMeshValue_zero, covariance_const_left, hT]
  | succ i =>
    have he : (fun x : Fin (n + 1) → ℝ ↦ observationMeshValue x (i + 1)) =
        fun x ↦ x (⟨i, by omega⟩ : Fin n).castSucc :=
      funext fun x ↦ observationMeshValue_succ x ⟨i, by omega⟩
    rw [he, gaussianCoordinateLaw_covariance _ hK]
    change min (T (i + 1)) (T (n + 1)) = T (i + 1)
    exact min_eq_left (timeGridTime_mono T (n + 1)
      (fun j hj ↦ by linarith [hgap j hj]) (by omega) le_rfl)

theorem gaussianGridInterpolation_site_covariance (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hT : T 0 = 0) (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j)
    (v : ℝ) (hv : 0 ≤ v) (hv' : v ≤ T n) :
    cov[fun x ↦ timeGridInterpolation T (observationMeshValue x) n v,
      fun x ↦ x (Fin.last n); gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))] = v := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  obtain ⟨k, hk, hkl, hku⟩ := exists_timeGridInterval T n hn v (by simpa only [hT] using hv) hv'
  have he : (fun x : Fin (n + 1) → ℝ ↦ timeGridInterpolation T (observationMeshValue x) n v) =
      (1 - (v - T k) / (T (k + 1) - T k)) • (fun x ↦ observationMeshValue x k) +
      ((v - T k) / (T (k + 1) - T k)) • (fun x ↦ observationMeshValue x (k + 1)) :=
    funext fun x ↦ timeGridInterpolation_interval T (observationMeshValue x) n k hg hk v hkl hku
  rw [he, covariance_add_left ((observationMeshValue_memLp n k K).const_smul _)
    ((observationMeshValue_memLp n (k + 1) K).const_smul _)
    (gaussianCoordinateLaw_coordinate_memLp_two K (Fin.last n)),
    covariance_smul_left, covariance_smul_left,
    observationMeshValue_site_covariance T n hT hgap k (by omega),
    observationMeshValue_site_covariance T n hT hgap (k + 1) (by omega)]
  field_simp [ne_of_gt (sub_pos.mpr (hg k hk))]
  <;> ring

theorem gaussianGridPath_site_covariance (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hT : T 0 = 0) (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j)
    (v : ℝ) (hv : 0 ≤ v) (hv' : v ≤ T n) :
    cov[fun p ↦ gaussianGridPath T n p v, fun p ↦ p.1 (Fin.last n);
      (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)] = v := by
  let K := brownianTimeMatrix T (n + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  obtain ⟨k, hk, hkl, hku⟩ := exists_timeGridInterval T n hn v (by simpa only [hT] using hv) hv'
  have hi := timeGridInterpolation_memLp (gaussianCoordinateLaw K) T
    (fun j x ↦ observationMeshValue x j) n k hg hk v hkl hku
    (observationMeshValue_memLp n k K) (observationMeshValue_memLp n (k + 1) K)
  have hh := covariance_product_sums (gaussianCoordinateLaw K) (independentBridgeLaw ℕ)
    (fun x ↦ timeGridInterpolation T (observationMeshValue x) n v)
    (fun x ↦ x (Fin.last n)) (fun ω ↦ timeGridBridge T n ω v) (fun _ ↦ 0)
    hi (gaussianCoordinateLaw_coordinate_memLp_two K (Fin.last n))
    (timeGridBridge_memLp_inside T n k hg hk v hkl hku) (memLp_const 0)
  simp only [add_zero, covariance_const_right] at hh
  exact hh.trans (gaussianGridInterpolation_site_covariance T n hn hT hgap v hv hv')

end SRWTightness
