import SRWTightness.TimeGridInterpolation
import Mathlib.Topology.ContinuousMap.Algebra

namespace SRWTightness

/-- Every mesh observation is preserved exactly. -/
theorem timeGridInterpolation_node (T x : ℕ → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k ≤ n) :
    timeGridInterpolation T x n (T k) = x k := by
  by_cases hn : n = 0
  · subst n
    have : k = 0 := by omega
    subst k
    simp [timeGridInterpolation]
  by_cases hkn : k < n
  · simpa using timeGridInterpolation_interval T x n k hgap hkn (T k) le_rfl
      (hgap k hkn).le
  · have he : k = n := by omega
    subst k
    have hs : n - 1 + 1 = n := by omega
    have hg := hgap (n - 1) (by omega)
    rw [hs] at hg
    have hh := timeGridInterpolation_interval T x n (n - 1) hgap (by omega) (T n)
      hg.le (by rw [hs])
    rw [hs, div_self (sub_ne_zero.mpr (ne_of_gt hg))] at hh
    simpa using hh

/-- A time between the mesh endpoints belongs to an adjacent mesh interval. -/
theorem exists_timeGridInterval (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (v : ℝ)
    (hl : T 0 ≤ v) (hu : v ≤ T n) : ∃ k < n, T k ≤ v ∧ v ≤ T (k + 1) := by
  induction n generalizing v with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by omega, hl, hu⟩
    by_cases hv : v ≤ T n
    · obtain ⟨k, hk, hkl, hku⟩ := ih (by omega) v hl hv
      exact ⟨k, by omega, hkl, hku⟩
    · exact ⟨n, by omega, (lt_of_not_ge hv).le, hu⟩

/-- Interpolation commutes with subtracting deterministic data. -/
theorem timeGridInterpolation_sub (T x y : ℕ → ℝ) (n : ℕ) (v : ℝ) :
    timeGridInterpolation T (x - y) n v =
      timeGridInterpolation T x n v - timeGridInterpolation T y n v := by
  unfold timeGridInterpolation
  simp only [Pi.sub_apply, sub_sub_sub_comm, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Linear time data interpolate to the same linear function on the entire mesh. -/
theorem timeGridInterpolation_linear_time (T : ℕ → ℝ) (n : ℕ)
    (hn : 0 < n) (hgap : ∀ j < n, T j < T (j + 1)) (c v : ℝ)
    (hl : T 0 ≤ v) (hu : v ≤ T n) :
    timeGridInterpolation T (fun j ↦ c * T j) n v = c * v := by
  obtain ⟨k, hk, hkl, hku⟩ := exists_timeGridInterval T n hn v hl hu
  rw [timeGridInterpolation_interval T _ n k hgap hk v hkl hku]
  have he : T (k + 1) - T k ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hgap k hk))
  field_simp
  <;> ring

/-- Subtracting the source mean before interpolation subtracts the same linear drift. -/
theorem timeGridInterpolation_centered (T x : ℕ → ℝ) (n : ℕ)
    (hn : 0 < n) (hgap : ∀ j < n, T j < T (j + 1)) (c v : ℝ)
    (hl : T 0 ≤ v) (hu : v ≤ T n) :
    timeGridInterpolation T (fun j ↦ x j - c * T j) n v =
      timeGridInterpolation T x n v - c * v := by
  rw [show (fun j ↦ x j - c * T j) = x - (fun j ↦ c * T j) from rfl,
    timeGridInterpolation_sub, timeGridInterpolation_linear_time T n hn hgap c v hl hu]

noncomputable def timeGridPath (T x : ℕ → ℝ) (n : ℕ) : C(ℝ, ℝ) :=
  ⟨timeGridInterpolation T x n, timeGridInterpolation_continuous T x n⟩

/-- Removing the interpolation leaves a continuous residual vanishing at every mesh point. -/
theorem timeGridResidual_nodes (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (p : C(ℝ, ℝ)) (k : ℕ) (hk : k ≤ n) :
    (p - timeGridPath T (fun j ↦ p (T j)) n) (T k) = 0 := by
  change p (T k) - timeGridInterpolation T (fun j ↦ p (T j)) n (T k) = 0
  rw [timeGridInterpolation_node T _ n k hgap hk, sub_self]

end SRWTightness
