import SRWTightness.SourceGaussianParameters
import SRWTightness.ReferenceCapacityFromEnergy
import SRWTightness.DiskObservationIndex

namespace SRWTightness

/-- The maximal disk in the source construction has an admissible reference-mark mass. -/
theorem source_reference_capacity (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      sourceReferenceIntensity (sourceLowerRadius t) 14 *
        capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
          (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ≤ 1 := by
  obtain ⟨I, hI, hα, hR⟩ := source_gaussian_parameters t A hA ht
  refine ⟨I, hI, ?_⟩
  obtain ⟨ha, hq, _, houter, htime, _⟩ := diskGaussianParameterChoice A
    (Real.exp 1 * sourceLowerRadius t + 14)
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (I + 1)
    (diskPointGaussianMinimumRadius_ge_base.trans hA) hα (by simpa using hR)
  simp only [Nat.add_sub_cancel] at houter htime
  have hpow : 1 ≤ diskEnergyGapRatio ^ I := one_le_pow₀ (by linarith)
  have ha1 : 1 ≤ A * diskEnergyGapRatio ^ I := by nlinarith
  have ha0 : 0 < A * diskEnergyGapRatio ^ I := by linarith
  have hKD : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)) ⊆
      translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)) := by
    apply Finset.image_subset_image
    exact diskFinset_mono _ _ ha0.le (by linarith)
  have hne : (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))).Nonempty :=
    Finset.Nonempty.image ⟨0, zero_mem_diskFinset _ ha0⟩ _
  apply reference_capacity_le_one_of_energy _ _ hKD hne _ _ (by positivity) hα
  rw [equilibriumEnergyTime_translate]
  exact equilibriumEnergyTime_disk_ge_one _ _ _ ha1 houter htime

end SRWTightness
