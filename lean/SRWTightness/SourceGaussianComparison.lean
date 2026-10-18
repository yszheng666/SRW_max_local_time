import SRWTightness.SourceGaussianParameters
import SRWTightness.GaussianDiskFixedParameters

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Complete Gaussian event comparison at the original m(t), H_0=14, alpha and maximal scale.
The event-specific correction moment is needed only for the conditional lower bound. -/
theorem source_gaussian_comparison {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      (let R := Real.exp 1 * sourceLowerRadius t + 14
       let α := sourceReferenceIntensity (sourceLowerRadius t) 14
       let K := brownianTimeMatrix (geometricDiskPointTime R A diskEnergyGapRatio α (I + 1)) (I + 2)
       let e := geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) (I + 1)
       (K - Matrix.diagonal e).PosDef ∧
       (gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν ≤
         ENNReal.ofReal (Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)))) •
           ((gaussianCoordinateLaw K).prod ν) ∧
       ∀ (s : Set (((Fin (I + 2)) → ℝ) × β)), MeasurableSet s → ∀ C : ℝ,
         (∫ x in s, gaussianInverseCorrection K (K - Matrix.diagonal e) x.1
           ∂(gaussianCoordinateLaw K).prod ν ≤ C * ((gaussianCoordinateLaw K).prod ν).real s) →
         Real.exp (-C / 2) * ((gaussianCoordinateLaw K).prod ν).real s ≤
           ((gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν).real s) := by
  obtain ⟨I, hI, hα, hR⟩ := source_gaussian_parameters t A hA ht
  refine ⟨I, hI, ?_⟩
  exact gaussian_disk_fixed_parameters ν b (Real.exp 1 * sourceLowerRadius t + 14) A
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (by omega : 0 < I + 1) hA hα
    (by simpa using hR)

end SRWTightness
