import SRWTightness.BridgedGridCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem bridgedGridPath_covariance_same {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k < n) (s t : ℝ)
    (hs : T k ≤ s) (hs' : s ≤ T (k + 1)) (ht : T k ≤ t) (ht' : t ≤ T (k + 1))
    (hX : ∀ j ≤ n, MemLp (X j) 2 μ)
    (hc : ∀ i ≤ n, ∀ j ≤ n, cov[X i, X j; μ] = min (T i) (T j)) :
    cov[fun p ↦ bridgedGridPath T X n p s, fun p ↦ bridgedGridPath T X n p t;
      μ.prod (independentBridgeLaw ℕ)] = min s t := by
  rw [bridgedGridPath_covariance_sum μ T X n k k hgap hk hk s t hs hs' ht ht' hX,
    timeGridInterpolation_brownian_covariance_same μ T X n k hgap hk s t hs hs' ht ht' hX hc,
    timeGridBridge_covariance_same T n k hgap hk s t hs hs' ht ht']
  rcases le_total s t with h | h
  · rw [min_eq_left h, min_eq_left (sub_le_sub_right h _)]
    ring
  · rw [min_eq_right h, min_eq_right (sub_le_sub_right h _)]
    ring

theorem bridgedGridPath_covariance_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n i j : ℕ)
    (hgap : ∀ k < n, T k < T (k + 1)) (hi : i < n) (hj : j < n) (hij : i < j)
    (s t : ℝ) (hs : T i ≤ s) (hs' : s ≤ T (i + 1))
    (ht : T j ≤ t) (ht' : t ≤ T (j + 1)) (hX : ∀ k ≤ n, MemLp (X k) 2 μ)
    (hc : ∀ k ≤ n, ∀ l ≤ n, cov[X k, X l; μ] = min (T k) (T l)) :
    cov[fun p ↦ bridgedGridPath T X n p s, fun p ↦ bridgedGridPath T X n p t;
      μ.prod (independentBridgeLaw ℕ)] = min s t := by
  rw [bridgedGridPath_covariance_sum μ T X n i j hgap hi hj s t hs hs' ht ht' hX,
    timeGridInterpolation_brownian_covariance_lt μ T X n i j hgap hi hj hij s t hs hs' ht ht' hX hc,
    timeGridBridge_covariance_ne T n i j hgap hi hj (ne_of_lt hij) s t hs hs' ht ht', add_zero]
  exact (min_eq_left (hs'.trans ((timeGridTime_mono T n hgap
    (Nat.succ_le_of_lt hij) (Nat.le_of_lt hj)).trans ht))).symm

/-- The actual independent bridges restore Brownian covariance throughout the mesh interval. -/
theorem bridgedGridPath_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hn : 0 < n) (hgap : ∀ k < n, T k < T (k + 1)) (s t : ℝ)
    (hs : T 0 ≤ s) (hs' : s ≤ T n) (ht : T 0 ≤ t) (ht' : t ≤ T n)
    (hX : ∀ k ≤ n, MemLp (X k) 2 μ)
    (hc : ∀ k ≤ n, ∀ l ≤ n, cov[X k, X l; μ] = min (T k) (T l)) :
    cov[fun p ↦ bridgedGridPath T X n p s, fun p ↦ bridgedGridPath T X n p t;
      μ.prod (independentBridgeLaw ℕ)] = min s t := by
  obtain ⟨i, hi, hil, hiu⟩ := exists_timeGridInterval T n hn s hs hs'
  obtain ⟨j, hj, hjl, hju⟩ := exists_timeGridInterval T n hn t ht ht'
  rcases lt_trichotomy i j with hij | hij | hij
  · exact bridgedGridPath_covariance_lt μ T X n i j hgap hi hj hij s t hil hiu hjl hju hX hc
  · subst j
    exact bridgedGridPath_covariance_same μ T X n i hgap hi s t hil hiu hjl hju hX hc
  · rw [covariance_comm, min_comm s t]
    exact bridgedGridPath_covariance_lt μ T X n j i hgap hj hi hij t s hjl hju hil hiu hX hc

end SRWTightness
