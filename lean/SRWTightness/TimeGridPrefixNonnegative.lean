import SRWTightness.TimeGridInterpolationNodes

namespace SRWTightness

/-- Nonnegative retained nodal corrections remain nonnegative along the interpolated prefix. -/
theorem timeGridInterpolation_prefix_nonneg (T x : ℕ → ℝ) (n k : ℕ)
    (hk : k ≤ n) (hkpos : 0 < k) (hgap : ∀ j < n, T j < T (j + 1))
    (hx : ∀ j ≤ k, 0 ≤ x j) (v : ℝ) (hl : T 0 ≤ v) (hu : v ≤ T k) :
    0 ≤ timeGridInterpolation T x n v := by
  obtain ⟨j, hj, hjl, hju⟩ := exists_timeGridInterval T k hkpos v hl hu
  have hjn : j < n := by omega
  rw [timeGridInterpolation_interval T x n j hgap hjn v hjl hju]
  have hden : 0 < T (j + 1) - T j := sub_pos.mpr (hgap j hjn)
  have hlo : 0 ≤ (v - T j) / (T (j + 1) - T j) :=
    div_nonneg (sub_nonneg.mpr hjl) hden.le
  have hup : (v - T j) / (T (j + 1) - T j) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hup) (hx j (by omega)))
    (mul_nonneg hlo (hx (j + 1) (by omega)))

end SRWTightness
