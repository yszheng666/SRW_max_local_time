import SRWTightness.GeometricDiskEnergyTimes

namespace SRWTightness

/-- A direct lower bound on the actual capacity-based observation time. -/
theorem equilibriumEnergyTime_disk_log_lower (R a α : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R) :
    Real.log (R / a) - diskGreenEnergyConstant / (2 / Real.pi) - α / (2 * (2 / Real.pi)) ≤
      equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) := by
  have hh := (abs_le.mp (capacity_energy_radius_bound R a ha hRa)).1
  unfold equilibriumEnergyTime
  linarith

/-- A logarithmic separation condition supplies the first positive Brownian time. -/
theorem equilibriumEnergyTime_disk_ge_one (R a α : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R)
    (hlog : 1 + diskGreenEnergyConstant / (2 / Real.pi) + α / (2 * (2 / Real.pi)) ≤
      Real.log (R / a)) :
    1 ≤ equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) := by
  have hh := equilibriumEnergyTime_disk_log_lower R a α ha hRa
  linarith

/-- Uniform unit gaps follow entirely from radius and logarithmic separation conditions. -/
theorem geometricDiskEnergyTime_gaps_of_radius (R A q α : ℝ) (n : ℕ) (hA : 1 ≤ A)
    (hq : 1 ≤ q)
    (hlog : 1 + 2 * (diskGreenEnergyConstant / (2 / Real.pi)) ≤ Real.log q)
    (hsep : ∀ i < n, 2 * (A * q ^ i) ≤ R)
    (houter : 2 * (A * q ^ (n - 1)) ≤ R)
    (htime : 1 + diskGreenEnergyConstant / (2 / Real.pi) + α / (2 * (2 / Real.pi)) ≤
      Real.log (R / (A * q ^ (n - 1)))) :
    ∀ k < n, 1 ≤ geometricDiskEnergyTime R A q α n (k + 1) -
      geometricDiskEnergyTime R A q α n k := by
  have hp : 1 ≤ q ^ (n - 1) := one_le_pow₀ hq
  have ha : 1 ≤ A * q ^ (n - 1) := by nlinarith
  exact geometricDiskEnergyTime_gaps R A q α n hA hq hlog hsep
    (equilibriumEnergyTime_disk_ge_one _ _ _ ha houter htime)

end SRWTightness
