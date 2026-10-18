import SRWTightness.GeometricDiskObservationCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- All four component identities for equilibrium averages and the retained center coordinate. -/
theorem geometric_disk_covariance_components {n : ℕ} (b : Site) (R A q : ℝ)
    (hA : 4 ≤ A) (hq : 2 ≤ q)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R)
    (M : Finset Site) (hKM : ∀ i, geometricDiskFamily b A q n i ⊆ M)
    (hMD : M ⊆ translateFinset b (diskFinset R)) (z : M) (hz : (z : Site) = b)
    (α u : ℝ) (hα : 0 < α) (hu : 0 < u)
    (hcap : α * capacity (translateFinset b (diskFinset R)) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let D := translateFinset b (diskFinset R)
    let K := geometricDiskFamily b A q n
    let μ := markProductLaw D M α k
    let S := fun i ↦ normalizedEquilibriumAverage D M (K i) k α (2 / Real.pi) u
    let F := normalizedMarkSum M k α (2 / Real.pi) u z
    let v := fun i ↦ equilibriumEnergyTime D (K i) α (2 / Real.pi)
    (∀ i, covariance (S i) (S i) μ = v i - equilibriumDiscreteError D (K i) (2 / Real.pi)) ∧
    (∀ i j, i ≠ j → covariance (S i) (S j) μ = min (v i) (v j)) ∧
    (∀ i, covariance F (S i) μ = v i) ∧
    covariance F F μ = pointEnergyTime D b α (2 / Real.pi) := by
  dsimp only
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hcov := geometric_disk_observation_covariance b R A q hA hq hsep M hKM hMD z hz
    α (2 / Real.pi) u hα hg hu hcap k hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [normalizedObservation, observationEnergyTime, observationDiscreteError,
      min_self, ite_true] using hcov (some i) (some i)
  · intro i j hij
    simpa only [normalizedObservation, observationEnergyTime, Option.some.injEq,
      if_neg hij, sub_zero] using hcov (some i) (some j)
  · intro i
    have hzi : (z : Site) ∈ geometricDiskFamily b A q n i := by
      rw [hz]
      exact geometricDiskFamily_center_mem b A q n (by linarith) (by linarith) i
    have hz0 : equilibriumWeight (translateFinset b (diskFinset R))
        (geometricDiskFamily b A q n i) z = 0 := by
      rw [hz]
      exact geometricDiskFamily_center_weight_zero b A R q n hA hq hsep i
    rw [normalizedEquilibriumAverage_coordinate_covariance _ M _ (hKM i) hMD z hzi
      α (2 / Real.pi) u hα hg hu hcap k hk, hz0, zero_div, sub_zero]
    rfl
  · simpa only [normalizedObservation, observationEnergyTime, observationDiscreteError,
      min_self, ite_true, sub_zero] using hcov none none

end SRWTightness
