import SRWTightness.ObservationSiteTilt
import SRWTightness.SourceObservationCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual source vector has probability weights, exact site tilt, and the source Gaussian mean. -/
theorem source_observation_site_tilt (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let D := translateFinset b (diskFinset R)
      let K := geometricDiskFamily b A diskEnergyGapRatio (I + 1)
      ∃ z : M, (z : Site) = b ∧
        let w := orderedObservationWeight D M K z
        (∀ i x, 0 ≤ w i x) ∧ (∀ i, ∑ x : M, w i x = 1) ∧
        ∀ (k : ℕ) (u : ℝ), 0 < u → u ^ 2 / 2 = (k : ℝ) →
          let F := fun i ↦ normalizedWeightedSum M k α (2 / Real.pi) u (w i)
          (∀ Y, (∑ j, siteTiltCoefficient (Fin.last (I + 1)) j * F j Y) =
            2 * normalizedMarkSum M k α (2 / Real.pi) u z Y) ∧
          ∀ i : Fin ((I + 1) + 1),
            (∑ j, siteTiltCoefficient (Fin.last (I + 1)) j *
              covariance (F i) (F j) (markProductLaw D M α k)) =
              2 * geometricDiskPointTime R A diskEnergyGapRatio α (I + 1) (i.val + 1) := by
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
  have hz (i : Fin (I + 1)) := geometricDiskFamily_center_mem b A diskEnergyGapRatio
    (I + 1) (by linarith) (by linarith) i
  have hKM (i : Fin (I + 1)) := geometricDiskFamily_mono b A diskEnergyGapRatio (I + 1)
    (by linarith) (by linarith) (Fin.le_last i)
  have hMD := geometricDiskFamily_subset b A _ diskEnergyGapRatio (I + 1)
    (by linarith) (by linarith) hsep (Fin.last I)
  have hzero (i : Fin (I + 1)) := geometricDiskFamily_center_weight_zero b A
    (Real.exp 1 * sourceLowerRadius t + 14) diskEnergyGapRatio (I + 1) ha hq hsep i
  let z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)) := ⟨b, hz (Fin.last I)⟩
  refine ⟨I, hI, z, rfl, ?_⟩
  have hw := orderedObservationWeight_probability _ _ _ z hKM hMD (fun i ↦ ⟨b, hz i⟩)
  refine ⟨hw.1, hw.2, ?_⟩
  intro k u hu hk
  constructor
  · intro Y
    rw [siteTiltCoefficient_sum]
    simp only [orderedObservationWeight, normalizedWeightedSum_observationWeight,
      diskObservationIndex_last, normalizedObservation]
  · intro i
    have hh := orderedObservation_site_tilt_target _ _ _ z hKM hMD hz hzero
      _ (2 / Real.pi) u hαpos (by positivity) hu hcap k hk i
    rw [diskObservationIndex_energy] at hh
    exact hh

end SRWTightness
