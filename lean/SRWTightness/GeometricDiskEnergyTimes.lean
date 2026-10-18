import SRWTightness.EquilibriumEnergySpacing
import SRWTightness.BrownianTimeCovariance

namespace SRWTightness

/-- Increasing time order for the energies at decreasing geometric disk radii. -/
noncomputable def geometricDiskEnergyTime (R A q α : ℝ) (n k : ℕ) : ℝ :=
  if k = 0 then 0 else
    equilibriumEnergyTime (diskFinset R) (diskFinset (A * q ^ (n - k))) α (2 / Real.pi)

@[simp] theorem geometricDiskEnergyTime_zero (R A q α : ℝ) (n : ℕ) :
    geometricDiskEnergyTime R A q α n 0 = 0 := by simp [geometricDiskEnergyTime]

/-- A sufficiently large fixed radius ratio gives unit gaps, provided the outermost time is at least one. -/
theorem geometricDiskEnergyTime_gaps (R A q α : ℝ) (n : ℕ) (hA : 1 ≤ A) (hq : 1 ≤ q)
    (hlog : 1 + 2 * (diskGreenEnergyConstant / (2 / Real.pi)) ≤ Real.log q)
    (hsep : ∀ i < n, 2 * (A * q ^ i) ≤ R)
    (hfirst : 1 ≤ equilibriumEnergyTime (diskFinset R)
      (diskFinset (A * q ^ (n - 1))) α (2 / Real.pi)) :
    ∀ k < n, 1 ≤ geometricDiskEnergyTime R A q α n (k + 1) -
      geometricDiskEnergyTime R A q α n k := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simpa [geometricDiskEnergyTime] using hfirst
  · have he : n - k = (n - (k + 1)) + 1 := by omega
    have hpow : 1 ≤ q ^ (n - (k + 1)) := one_le_pow₀ hq
    have ha : 1 ≤ A * q ^ (n - (k + 1)) := by nlinarith
    have hr : 2 * (q * (A * q ^ (n - (k + 1)) )) ≤ R := by
      have hh := hsep (n - k) (by omega)
      rw [he, pow_succ] at hh
      nlinarith
    have hh := disk_equilibriumEnergy_geometric_spacing R
      (A * q ^ (n - (k + 1))) q α ha hq hr
    have hl := (abs_le.mp hh).1
    have hb : A * q ^ (n - k) = q * (A * q ^ (n - (k + 1))) := by
      rw [he, pow_succ]
      ring
    simp only [geometricDiskEnergyTime, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ↓reduceIte, hk0, hb]
    linarith

end SRWTightness
