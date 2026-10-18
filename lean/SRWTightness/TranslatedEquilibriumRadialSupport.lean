import SRWTightness.EquilibriumBoundarySupport
import SRWTightness.LatticeTranslation
import SRWTightness.DiskCapacityLogBound

namespace SRWTightness

/-- The enclosing disk equilibrium charge is supported on its inner unit boundary layer. -/
theorem translated_equilibrium_radial_support (b : Site) (r R : ℝ)
    (hr : 2 ≤ r) (hrR : r ≤ R) (x : Site)
    (hx : x ∈ translateFinset b (diskFinset r))
    (he : equilibriumMeasure (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset r)) x ≠ 0) :
    r - 1 ≤ Real.sqrt (normSq (x - b)) ∧ Real.sqrt (normSq (x - b)) ≤ r := by
  have htrans := equilibriumMeasure_translate b (diskFinset R) (diskFinset r) (x - b)
  rw [show b + (x - b) = x by abel] at htrans
  have he' : equilibriumMeasure (diskFinset R) (diskFinset r) (x - b) ≠ 0 := by
    rwa [htrans] at he
  have hlo := disk_equilibrium_support_lower (diskFinset R) r hr
    (diskFinset_mono r R (by linarith) hrR) (x - b) he'
  have hhi : normSq (x - b) < r ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hx
  have hs := Real.sq_sqrt (normSq_nonneg (x - b))
  have hn := Real.sqrt_nonneg (normSq (x - b))
  constructor <;> nlinarith

end SRWTightness
