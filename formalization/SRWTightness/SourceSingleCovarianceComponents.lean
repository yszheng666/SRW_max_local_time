import SRWTightness.GeometricDiskCovarianceComponents
import SRWTightness.SourceObservationCovariance
import SRWTightness.SourcePointEnergyTime

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The four literal single-site covariance components on the actual maximal observation domain. -/
theorem source_single_covariance_components (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      ∃ z : M, (z : Site) = b ∧ ∀ (k : ℕ) (u : ℝ), 0 < u → u ^ 2 / 2 = (k : ℝ) →
        let D := translateFinset b (diskFinset R)
        let K := geometricDiskFamily b A diskEnergyGapRatio (I + 1)
        let μ := markProductLaw D M α k
        let S := fun i ↦ normalizedEquilibriumAverage D M (K i) k α (2 / Real.pi) u
        let F := normalizedMarkSum M k α (2 / Real.pi) u z
        let v := fun i ↦ equilibriumEnergyTime D (K i) α (2 / Real.pi)
        let V := sourcePointEnergyTime b (sourceLowerRadius t) 14
        (∀ i, covariance (S i) (S i) μ =
          v i - equilibriumDiscreteError D (K i) (2 / Real.pi)) ∧
        (∀ i j, i ≠ j → covariance (S i) (S j) μ = min (v i) (v j)) ∧
        (∀ i, covariance F (S i) μ = v i) ∧ covariance F F μ = V ∧
        |V - sourceLowerTime (sourceLowerRadius t)| ≤
          sourcePointEnergyTimeError + sourceLowerTimeError := by
  obtain ⟨I, hI, hcap⟩ := source_reference_capacity b t A hA ht
  obtain ⟨J, hJ, hα, hR⟩ := source_gaussian_parameters t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  obtain ⟨ha, hq, hsep, _, _, _⟩ := diskGaussianParameterChoice A
    (Real.exp 1 * sourceLowerRadius t + 14)
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (I + 1)
    (diskPointGaussianMinimumRadius_ge_base.trans hA) hα (by simpa using hR)
  have hm70 := (sourceScaleThreshold_conditions t A ha
    ((le_max_left _ _).trans ht)).2.2.1
  have hαpos := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1
  have hz := geometricDiskFamily_center_mem b A diskEnergyGapRatio (I + 1)
    (by linarith) (by linarith) (Fin.last I)
  refine ⟨I, hI, ⟨b, hz⟩, rfl, ?_⟩
  intro k u hu hk
  have hc := geometric_disk_covariance_components b
    (Real.exp 1 * sourceLowerRadius t + 14) A diskEnergyGapRatio ha hq hsep _
    (fun i ↦ geometricDiskFamily_mono b A diskEnergyGapRatio (I + 1)
      (by linarith) (by linarith) (Fin.le_last i))
    (geometricDiskFamily_subset b A _ diskEnergyGapRatio (I + 1)
      (by linarith) (by linarith) hsep (Fin.last I)) ⟨b, hz⟩ rfl _ u hαpos hu hcap k hk
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2,
    sourcePointEnergyTime_lowerTime_bound b (sourceLowerRadius t) 14
      (by linarith) (by norm_num) (by linarith)⟩

end SRWTightness
