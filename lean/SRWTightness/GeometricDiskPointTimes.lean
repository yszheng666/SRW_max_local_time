import SRWTightness.DiskPointEnergyGap
import SRWTightness.GeometricDiskEnergyTimes

namespace SRWTightness

noncomputable def geometricDiskPointTime (R A q α : ℝ) (n k : ℕ) : ℝ :=
  if k ≤ n then geometricDiskEnergyTime R A q α n k else
    pointEnergyTime (diskFinset R) 0 α (2 / Real.pi)

@[simp] theorem geometricDiskPointTime_zero (R A q α : ℝ) (n : ℕ) :
    geometricDiskPointTime R A q α n 0 = 0 := by
  simp [geometricDiskPointTime]

/-- The final center-point coordinate also has a unit time gap at sufficiently large inner radius. -/
theorem geometricDiskPointTime_gaps (R A q α : ℝ) (n : ℕ) (hn : 0 < n)
    (hA : 1 ≤ A) (hq : 1 ≤ q)
    (hlog : 1 + 2 * (diskGreenEnergyConstant / (2 / Real.pi)) ≤ Real.log q)
    (hsep : ∀ i < n, 2 * (A * q ^ i) ≤ R)
    (hfirst : 1 ≤ equilibriumEnergyTime (diskFinset R)
      (diskFinset (A * q ^ (n - 1))) α (2 / Real.pi))
    (hpoint : 1 + diskPointEnergyGapConstant ≤ Real.log A) :
    ∀ k < n + 1, 1 ≤ geometricDiskPointTime R A q α n (k + 1) -
      geometricDiskPointTime R A q α n k := by
  intro k hk
  by_cases hkn : k < n
  · have hs : k + 1 ≤ n := by omega
    simp only [geometricDiskPointTime, hs, hkn.le, ↓reduceIte]
    exact geometricDiskEnergyTime_gaps R A q α n hA hq hlog hsep hfirst k hkn
  · have he : k = n := by omega
    subst k
    have hRa : 2 * A ≤ R := by simpa using hsep 0 hn
    have hh := disk_point_energy_gap_ge_one R A α hA hRa hpoint
    simpa [geometricDiskPointTime, geometricDiskEnergyTime, Nat.ne_of_gt hn] using hh

end SRWTightness
