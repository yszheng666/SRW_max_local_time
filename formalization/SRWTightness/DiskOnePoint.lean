import SRWTightness.DiskFiniteDomain
import SRWTightness.TailGeometric

namespace SRWTightness

/-- Green kernel of the actual walk killed on exiting the open Euclidean disk. -/
noncomputable def diskGreen (R : ℝ) (x y : Site) : ℝ :=
  killedGreen (diskFinset R) x y

 theorem domainLocalTime_disk (R : ℝ) (x : Site) (ω : Sample) :
    domainLocalTime (diskFinset R) 0 x ω = localTime ω (exitSteps R ω) x := by
  unfold domainLocalTime
  rw [domainSteps_disk, sub_zero]

/-- Manuscript (2.9), including the first-hitting prefactor and the half-open exit convention. -/
theorem disk_one_point_tail (R : ℝ) (x : Site) (hx : x ∈ disk R)
    (k : ℕ) (hk : 1 ≤ k) :
    pathLaw.real {ω | k ≤ localTime ω (exitSteps R ω) x} =
      (diskGreen R 0 x / diskGreen R x x) * (1 - 1 / diskGreen R x x) ^ (k - 1) := by
  simpa only [domainLocalTime_disk, diskGreen] using
    occupation_probability_ge (diskFinset R) 0 x ((mem_diskFinset R x).mpr hx) k hk

end SRWTightness
