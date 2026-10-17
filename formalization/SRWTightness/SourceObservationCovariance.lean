import SRWTightness.SourceReferenceCapacity
import SRWTightness.OrderedDiskObservationCovariance

open Matrix MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Actual source marks, on the actual maximal observation disk, have the ordered K-E covariance.
The statement does not identify the mark distribution with a Gaussian distribution. -/
theorem source_observation_covariance (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      ∃ z : M, (z : Site) = b ∧ ∀ (k : ℕ) (u : ℝ), 0 < u → u ^ 2 / 2 = (k : ℝ) →
        ∀ i j : Fin ((I + 1) + 1),
        covariance
          (normalizedObservation (translateFinset b (diskFinset R)) M
            (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z k α (2 / Real.pi) u
            (diskObservationIndex (I + 1) i))
          (normalizedObservation (translateFinset b (diskFinset R)) M
            (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z k α (2 / Real.pi) u
            (diskObservationIndex (I + 1) j))
          (markProductLaw (translateFinset b (diskFinset R)) M α k) =
        (brownianTimeMatrix (geometricDiskPointTime R A diskEnergyGapRatio α (I + 1))
            ((I + 1) + 1) -
          Matrix.diagonal (geometricDiskPointError b A R diskEnergyGapRatio
            (2 / Real.pi) (I + 1))) i j := by
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
  intro k u hu hk i j
  apply ordered_disk_observation_covariance b _ A diskEnergyGapRatio ha hq hsep _
    (fun i ↦ geometricDiskFamily_mono b A diskEnergyGapRatio (I + 1)
      (by linarith) (by linarith) (Fin.le_last i))
    (geometricDiskFamily_subset b A _ diskEnergyGapRatio (I + 1)
      (by linarith) (by linarith) hsep (Fin.last I)) _ rfl _ u hαpos hu hcap k hk i j

end SRWTightness
