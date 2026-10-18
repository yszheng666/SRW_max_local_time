import SRWTightness.DiskObservationIndex
import SRWTightness.GeometricDiskObservationCovariance

open Matrix MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Exact K-E covariance of actual reference marks in the full source coordinate order.
This is a covariance identity; it does not assert that the mark vector itself is Gaussian. -/
theorem ordered_disk_observation_covariance {n : ℕ} (b : Site) (R A q : ℝ)
    (hA : 4 ≤ A) (hq : 2 ≤ q)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R)
    (M : Finset Site) (hKM : ∀ i, geometricDiskFamily b A q n i ⊆ M)
    (hMD : M ⊆ translateFinset b (diskFinset R)) (z : M) (hz : (z : Site) = b)
    (α u : ℝ) (hα : 0 < α) (hu : 0 < u)
    (hcap : α * capacity (translateFinset b (diskFinset R)) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (i j : Fin (n + 1)) :
    covariance
      (normalizedObservation (translateFinset b (diskFinset R)) M (geometricDiskFamily b A q n)
        z k α (2 / Real.pi) u (diskObservationIndex n i))
      (normalizedObservation (translateFinset b (diskFinset R)) M (geometricDiskFamily b A q n)
        z k α (2 / Real.pi) u (diskObservationIndex n j))
      (markProductLaw (translateFinset b (diskFinset R)) M α k) =
    (brownianTimeMatrix (geometricDiskPointTime R A q α n) (n + 1) -
      Matrix.diagonal (geometricDiskPointError b A R q (2 / Real.pi) n)) i j := by
  have hh := geometric_disk_observation_covariance b R A q hA hq hsep M hKM hMD z hz
    α (2 / Real.pi) u hα (by positivity) hu hcap k hk
    (diskObservationIndex n i) (diskObservationIndex n j)
  rw [diskObservationIndex_energy, diskObservationIndex_energy, diskObservationIndex_error] at hh
  simpa only [(diskObservationIndex n).injective.eq_iff, Matrix.sub_apply,
    brownianTimeMatrix, Matrix.of_apply, Matrix.diagonal_apply] using hh

end SRWTightness
