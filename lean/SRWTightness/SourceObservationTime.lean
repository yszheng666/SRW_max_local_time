import SRWTightness.SourceObservationSpectralGap
import SRWTightness.SourceEquilibriumTime
import SRWTightness.SourcePointEnergyTime

namespace SRWTightness

/-- The source time mesh includes zero, all averages in increasing time order, then the site. -/
noncomputable def sourceObservationTime (t A : ℝ) (I j : ℕ) : ℝ :=
  geometricDiskPointTime (Real.exp 1 * sourceLowerRadius t + 14) A diskEnergyGapRatio
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (I + 1) j

@[simp] theorem sourceObservationTime_zero (t A : ℝ) (I : ℕ) :
    sourceObservationTime t A I 0 = 0 := by
  simp [sourceObservationTime]

/-- The final average time is exactly v_0, with the source translation retained. -/
theorem sourceObservationTime_last_average (b : Site) (t A : ℝ) (I : ℕ) :
    sourceObservationTime t A I (I + 1) =
      sourceEquilibriumTime b (sourceLowerRadius t) A 14 := by
  simp [sourceObservationTime, geometricDiskPointTime, geometricDiskEnergyTime,
    sourceEquilibriumTime, equilibriumEnergyTime_translate]

/-- The next time is the center variance V, outside the interpolated average path. -/
theorem sourceObservationTime_site (b : Site) (t A : ℝ) (I : ℕ) :
    sourceObservationTime t A I (I + 2) = sourcePointEnergyTime b (sourceLowerRadius t) 14 := by
  have hh := pointEnergyTime_translate b
    (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)) 0
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
  simp only [add_zero] at hh
  simp only [sourceObservationTime, geometricDiskPointTime,
    show ¬ I + 2 ≤ I + 1 by omega, ↓reduceIte, sourcePointEnergyTime]
  exact hh.symm

/-- Every actual source time gap is at least one, including the separate final site increment. -/
theorem sourceObservationTime_gaps (t A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : sourceGaussianThreshold A ≤ t) (I : ℕ)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) :
    ∀ j < (I + 1) + 1, 1 ≤ sourceObservationTime t A I (j + 1) -
      sourceObservationTime t A I j := by
  obtain ⟨J, hJ, hα, hR⟩ := source_gaussian_parameters t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  obtain ⟨ha, hq, hsep, houter, htime, _⟩ := diskGaussianParameterChoice A
    (Real.exp 1 * sourceLowerRadius t + 14)
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (I + 1)
    (diskPointGaussianMinimumRadius_ge_base.trans hA) hα (by simpa using hR)
  have hp : 1 ≤ diskEnergyGapRatio ^ ((I + 1) - 1) := one_le_pow₀ (by linarith)
  have harad : 1 ≤ A * diskEnergyGapRatio ^ ((I + 1) - 1) := by nlinarith
  have hfirst := equilibriumEnergyTime_disk_ge_one _ _ _ harad houter htime
  exact geometricDiskPointTime_gaps _ A diskEnergyGapRatio _ (I + 1) (by omega)
    (by linarith) (by linarith) diskEnergyGapRatio_log_lower
    (fun i hi ↦ hsep ⟨i, hi⟩) hfirst (diskPointGaussianMinimumRadius_log_gap A hA)

end SRWTightness
