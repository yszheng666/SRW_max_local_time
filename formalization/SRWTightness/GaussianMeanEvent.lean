import SRWTightness.GaussianMeanEntropy

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Gaussian density ratios are normalized and have integrable relative entropy. -/
theorem gaussianMeanDensityWeight_entropy_data {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    Integrable (gaussianMeanDensityWeight m K) (gaussianCoordinateLaw K) ∧
    (∫ x, gaussianMeanDensityWeight m K x ∂gaussianCoordinateLaw K) = 1 ∧
    Integrable (fun x ↦ gaussianMeanDensityWeight m K x * Real.log (gaussianMeanDensityWeight m K x))
      (gaussianCoordinateLaw K) := by
  letI := gaussianMeanCoordinateLaw_isProbabilityMeasure m K
  have hm := gaussianMeanDensityWeight_measurable m K
  have hn := gaussianMeanDensityWeight_nonneg m K
  have hconst : Integrable (fun _ : ι → ℝ ↦ (1 : ℝ))
      ((gaussianCoordinateLaw K).withDensity (fun x ↦ ENNReal.ofReal (gaussianMeanDensityWeight m K x))) := by
    rw [← gaussianMeanCoordinateLaw_changeDensity m K hK]
    exact integrable_const 1
  have hf := (integrable_nonnegative_density_iff (gaussianCoordinateLaw K)
    (gaussianMeanDensityWeight m K) hm hn (fun _ ↦ 1)).mp hconst
  have hf' : Integrable (gaussianMeanDensityWeight m K) (gaussianCoordinateLaw K) := by
    simpa only [mul_one] using hf
  have hmass := withDensity_ofReal_event_real (gaussianCoordinateLaw K)
    (gaussianMeanDensityWeight m K) hm hn Set.univ MeasurableSet.univ
  rw [← gaussianMeanCoordinateLaw_changeDensity m K hK] at hmass
  have hmass' : (∫ x, gaussianMeanDensityWeight m K x ∂gaussianCoordinateLaw K) = 1 := by
    simpa using hmass.symm
  have hi := gaussianMeanDensityWeight_log_integrable m K
  rw [gaussianMeanCoordinateLaw_changeDensity m K hK] at hi
  exact ⟨hf', hmass', (integrable_nonnegative_density_iff (gaussianCoordinateLaw K)
    (gaussianMeanDensityWeight m K) hm hn (fun x ↦ Real.log (gaussianMeanDensityWeight m K x))).mp hi⟩

/-- Mean shifts change every measurable Gaussian event by at most the entropy bound. -/
theorem gaussian_mean_event_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    |(gaussianMeanCoordinateLaw m K).real s - (gaussianCoordinateLaw K).real s| ≤
      2 * Real.sqrt ((m ⬝ᵥ (K⁻¹ *ᵥ m)) / 2) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hd := gaussianMeanDensityWeight_entropy_data m K hK
  have hh := density_entropy_event_bound (gaussianCoordinateLaw K) (gaussianMeanDensityWeight m K)
    (gaussianMeanDensityWeight_measurable m K) hd.1 (gaussianMeanDensityWeight_nonneg m K)
    hd.2.1 hd.2.2 s hs
  rw [← gaussianMeanCoordinateLaw_changeDensity m K hK, gaussian_mean_entropy_formula m K hK] at hh
  exact hh

/-- The mean-shift event bound also holds after adjoining independent auxiliary randomness. -/
theorem gaussian_mean_event_bound_aux {ι Ξ : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef)
    (s : Set ((ι → ℝ) × Ξ)) (hs : MeasurableSet s) :
    |((gaussianMeanCoordinateLaw m K).prod ν).real s -
      ((gaussianCoordinateLaw K).prod ν).real s| ≤
      2 * Real.sqrt ((m ⬝ᵥ (K⁻¹ *ᵥ m)) / 2) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hd := gaussianMeanDensityWeight_entropy_data m K hK
  have hh := density_entropy_event_bound_aux (gaussianCoordinateLaw K) ν
    (gaussianMeanDensityWeight m K) (gaussianMeanDensityWeight_measurable m K)
    hd.1 (gaussianMeanDensityWeight_nonneg m K) hd.2.1 hd.2.2 s hs
  rw [← gaussianMeanCoordinateLaw_changeDensity m K hK, gaussian_mean_entropy_formula m K hK] at hh
  exact hh

end SRWTightness
