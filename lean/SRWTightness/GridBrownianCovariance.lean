import SRWTightness.GridInterpolationCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem timeGridInterpolation_brownian_covariance_same {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k < n) (s t : ℝ)
    (hs : T k ≤ s) (hs' : s ≤ T (k + 1)) (ht : T k ≤ t) (ht' : t ≤ T (k + 1))
    (hX : ∀ j ≤ n, MemLp (X j) 2 μ)
    (hc : ∀ i ≤ n, ∀ j ≤ n, cov[X i, X j; μ] = min (T i) (T j)) :
    cov[fun ω ↦ timeGridInterpolation T (fun j ↦ X j ω) n s,
      fun ω ↦ timeGridInterpolation T (fun j ↦ X j ω) n t; μ] =
      T k + (s - T k) * (t - T k) / (T (k + 1) - T k) := by
  rw [timeGridInterpolation_covariance_nodes μ T X n k k hgap hk hk s t hs hs' ht ht' hX]
  rw [hc k (by omega) k (by omega), hc k (by omega) (k+1) (by omega),
    hc (k+1) (by omega) k (by omega), hc (k+1) (by omega) (k+1) (by omega)]
  rw [min_self, min_self, min_eq_left (hgap k hk).le, min_eq_right (hgap k hk).le]
  field_simp [ne_of_gt (sub_pos.mpr (hgap k hk))]
  <;> ring

theorem timeGridInterpolation_brownian_covariance_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n i j : ℕ)
    (hgap : ∀ k < n, T k < T (k + 1)) (hi : i < n) (hj : j < n) (hij : i < j)
    (s t : ℝ) (hs : T i ≤ s) (hs' : s ≤ T (i + 1))
    (ht : T j ≤ t) (ht' : t ≤ T (j + 1)) (hX : ∀ k ≤ n, MemLp (X k) 2 μ)
    (hc : ∀ k ≤ n, ∀ l ≤ n, cov[X k, X l; μ] = min (T k) (T l)) :
    cov[fun ω ↦ timeGridInterpolation T (fun k ↦ X k ω) n s,
      fun ω ↦ timeGridInterpolation T (fun k ↦ X k ω) n t; μ] = s := by
  rw [timeGridInterpolation_covariance_nodes μ T X n i j hgap hi hj s t hs hs' ht ht' hX]
  rw [hc i (by omega) j (by omega), hc i (by omega) (j+1) (by omega),
    hc (i+1) (by omega) j (by omega), hc (i+1) (by omega) (j+1) (by omega)]
  rw [min_eq_left (timeGridTime_mono T n hgap (by omega : i ≤ j) (by omega)),
    min_eq_left (timeGridTime_mono T n hgap (by omega : i ≤ j+1) (by omega)),
    min_eq_left (timeGridTime_mono T n hgap (by omega : i+1 ≤ j) (by omega)),
    min_eq_left (timeGridTime_mono T n hgap (by omega : i+1 ≤ j+1) (by omega))]
  field_simp [ne_of_gt (sub_pos.mpr (hgap i hi)), ne_of_gt (sub_pos.mpr (hgap j hj))]
  <;> ring

end SRWTightness
