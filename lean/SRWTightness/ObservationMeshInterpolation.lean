import SRWTightness.TimeGridInterpolationNodes

namespace SRWTightness

/-- Zero followed by the average coordinates; the final site coordinate is excluded. -/
noncomputable def observationMeshValue {n : ℕ} (x : Fin (n + 1) → ℝ) (j : ℕ) : ℝ :=
  if h : 0 < j ∧ j ≤ n then x ⟨j - 1, by omega⟩ else 0

@[simp] theorem observationMeshValue_zero {n : ℕ} (x : Fin (n + 1) → ℝ) :
    observationMeshValue x 0 = 0 := by simp [observationMeshValue]

@[simp] theorem observationMeshValue_succ {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin n) :
    observationMeshValue x (i.val + 1) = x i.castSucc := by
  simp [observationMeshValue, show i.val + 1 ≤ n by omega]
  rfl

theorem observationMeshValue_sub {n : ℕ} (x y : Fin (n + 1) → ℝ) :
    observationMeshValue (x - y) = observationMeshValue x - observationMeshValue y := by
  funext j
  simp only [observationMeshValue, Pi.sub_apply]
  split <;> simp

theorem timeGridInterpolation_congr (T x y : ℕ → ℝ) (n : ℕ)
    (hxy : ∀ j ≤ n, x j = y j) (v : ℝ) :
    timeGridInterpolation T x n v = timeGridInterpolation T y n v := by
  unfold timeGridInterpolation
  rw [hxy 0 (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hh := Finset.mem_range.mp hj
  rw [hxy j (by omega), hxy (j + 1) (by omega)]

/-- Continuous interpolation of just the ordered average observations. -/
noncomputable def orderedObservationPath {n : ℕ} (T : ℕ → ℝ)
    (x : Fin (n + 1) → ℝ) : C(ℝ, ℝ) := timeGridPath T (observationMeshValue x) n

theorem orderedObservationPath_node {n : ℕ} (T : ℕ → ℝ)
    (hgap : ∀ j < n, T j < T (j + 1)) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    orderedObservationPath T x (T (i.val + 1)) = x i.castSucc := by
  change timeGridInterpolation T (observationMeshValue x) n (T (i.val + 1)) = _
  rw [timeGridInterpolation_node T _ n _ hgap (by omega), observationMeshValue_succ]

theorem orderedObservationPath_zero {n : ℕ} (T : ℕ → ℝ)
    (hgap : ∀ j < n, T j < T (j + 1)) (x : Fin (n + 1) → ℝ) :
    orderedObservationPath T x (T 0) = 0 := by
  change timeGridInterpolation T (observationMeshValue x) n (T 0) = _
  rw [timeGridInterpolation_node T _ n 0 hgap (by omega), observationMeshValue_zero]

/-- Source Gaussian centering gives drift 2v throughout the entire average path. -/
theorem orderedObservationPath_centered {n : ℕ} (T : ℕ → ℝ) (hT : T 0 = 0)
    (hn : 0 < n) (hgap : ∀ j < n, T j < T (j + 1))
    (x : Fin (n + 1) → ℝ) (c v : ℝ) (hl : T 0 ≤ v) (hu : v ≤ T n) :
    orderedObservationPath T (x - (fun i ↦ c * T (i.val + 1))) v =
      orderedObservationPath T x v - c * v := by
  change timeGridInterpolation T
    (observationMeshValue (x - (fun i ↦ c * T (i.val + 1)))) n v = _
  rw [observationMeshValue_sub, timeGridInterpolation_sub]
  have hh : timeGridInterpolation T
      (observationMeshValue (fun i : Fin (n + 1) ↦ c * T (i.val + 1))) n v = c * v := by
    calc
      _ = timeGridInterpolation T (fun j ↦ c * T j) n v := by
        apply timeGridInterpolation_congr
        intro j hj
        by_cases hj0 : j = 0
        · subst j; simp [hT]
        · have hjpos : 0 < j := by omega
          simp [observationMeshValue, hjpos, hj, Nat.sub_add_cancel (by omega : 1 ≤ j)]
      _ = _ := timeGridInterpolation_linear_time T n hn hgap c v hl hu
  rw [hh]
  rfl

end SRWTightness
