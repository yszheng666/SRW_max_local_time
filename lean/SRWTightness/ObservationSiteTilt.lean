import SRWTightness.ObservationWeights

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The exact tilt by twice the site coordinate, in any finite coordinate order. -/
def siteTiltCoefficient {ι : Type*} [DecidableEq ι] (site i : ι) : ℝ :=
  if i = site then 2 else 0

@[simp] theorem siteTiltCoefficient_sum_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (site : ι) : ∑ i, |siteTiltCoefficient site i| = 2 := by
  simp only [siteTiltCoefficient]
  simp_rw [apply_ite abs]
  norm_num

@[simp] theorem siteTiltCoefficient_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (site : ι) (x : ι → ℝ) : ∑ i, siteTiltCoefficient site i * x i = 2 * x site := by
  simp [siteTiltCoefficient, ite_mul]

/-- The site covariance column is precisely the energy-time vector; there is no diagonal error. -/
theorem normalizedObservation_site_covariance {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) (hKM : ∀ i, K i ⊆ M) (hMD : M ⊆ D)
    (hz : ∀ i, (z : Site) ∈ K i) (hzero : ∀ i, equilibriumWeight D (K i) z = 0)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D M ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (i : Option (Fin n)) :
    covariance (normalizedObservation D M K z k α g u i)
      (normalizedMarkSum M k α g u z) (markProductLaw D M α k) =
      observationEnergyTime D K z α g i := by
  cases i with
  | none =>
    simp only [normalizedObservation, observationEnergyTime]
    rw [normalizedMarkSum_covariance D M hMD α g u hα hg hu hcap k hk]
    simp only [ite_true, pointEnergyTime]
    ring
  | some i =>
    simp only [normalizedObservation, observationEnergyTime]
    rw [covariance_comm,
      normalizedEquilibriumAverage_coordinate_covariance D M (K i) (hKM i) hMD z (hz i)
        α g u hα hg hu hcap k hk, hzero i, zero_div, sub_zero]
    rfl

/-- The target mean in the bounded-tilt comparison is twice each exact energy time. -/
theorem orderedObservation_site_tilt_target {n : ℕ} (D M : Finset Site)
    (K : Fin n → Finset Site) (z : M) (hKM : ∀ i, K i ⊆ M) (hMD : M ⊆ D)
    (hz : ∀ i, (z : Site) ∈ K i) (hzero : ∀ i, equilibriumWeight D (K i) z = 0)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D M ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), siteTiltCoefficient (Fin.last n) j *
      covariance
        (normalizedWeightedSum M k α g u (orderedObservationWeight D M K z i))
        (normalizedWeightedSum M k α g u (orderedObservationWeight D M K z j))
        (markProductLaw D M α k)) =
      2 * observationEnergyTime D K z α g (diskObservationIndex n i) := by
  rw [siteTiltCoefficient_sum]
  simp only [orderedObservationWeight, normalizedWeightedSum_observationWeight,
    diskObservationIndex_last, normalizedObservation]
  exact congrArg (fun x : ℝ ↦ 2 * x)
    (normalizedObservation_site_covariance D M K z hKM hMD hz hzero
      α g u hα hg hu hcap k hk (diskObservationIndex n i))

end SRWTightness
