import SRWTightness.GeometricDiskFamily
import SRWTightness.EquilibriumObservationMatrix

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The exact minimum-energy-minus-diagonal covariance with the nesting, shell separation,
and zero center weights discharged for the actual geometric disk family. -/
theorem geometric_disk_observation_covariance {n : ℕ} (b : Site) (R A q : ℝ)
    (hA : 4 ≤ A) (hq : 2 ≤ q)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R)
    (M : Finset Site) (hKM : ∀ i, geometricDiskFamily b A q n i ⊆ M)
    (hMD : M ⊆ translateFinset b (diskFinset R)) (z : M) (hz : (z : Site) = b)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity (translateFinset b (diskFinset R)) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (i j : Option (Fin n)) :
    covariance
      (normalizedObservation (translateFinset b (diskFinset R)) M (geometricDiskFamily b A q n)
        z k α g u i)
      (normalizedObservation (translateFinset b (diskFinset R)) M (geometricDiskFamily b A q n)
        z k α g u j)
      (markProductLaw (translateFinset b (diskFinset R)) M α k) =
    min (observationEnergyTime (translateFinset b (diskFinset R))
      (geometricDiskFamily b A q n) b α g i)
      (observationEnergyTime (translateFinset b (diskFinset R))
        (geometricDiskFamily b A q n) b α g j) -
      (if i = j then observationDiscreteError (translateFinset b (diskFinset R))
        (geometricDiskFamily b A q n) g i else 0) := by
  have hmono := geometricDiskFamily_mono b A q n (by linarith) (by linarith)
  have hdis := geometricDiskFamily_weights_disjoint b A R q n hA hq hsep
  have hcenter (i : Fin n) : (z : Site) ∈ geometricDiskFamily b A q n i := by
    rw [hz]
    exact geometricDiskFamily_center_mem b A q n (by linarith) (by linarith) i
  have hzero (i : Fin n) : equilibriumWeight (translateFinset b (diskFinset R))
      (geometricDiskFamily b A q n i) z = 0 := by
    rw [hz]
    exact geometricDiskFamily_center_weight_zero b A R q n hA hq hsep i
  simpa only [hz] using normalizedObservation_covariance _ M (geometricDiskFamily b A q n)
    hKM hMD hmono hdis z hcenter hzero α g u hα hg hu hcap k hk i j

end SRWTightness
