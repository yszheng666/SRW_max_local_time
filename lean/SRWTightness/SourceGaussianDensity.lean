import SRWTightness.SourceGaussianComparison
import SRWTightness.GaussianDiskFixedDensity

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Source-scale Gaussian density ratio, determinant factor, and quadratic correction bounds. -/
theorem source_gaussian_density (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let K := brownianTimeMatrix (geometricDiskPointTime R A diskEnergyGapRatio α (I + 1)) (I + 2)
      let e := geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) (I + 1)
      let S := K - Matrix.diagonal e
      let J := diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e
      K.PosDef ∧ S.PosDef ∧
      (1 ≤ (Real.sqrt (1 - J).det)⁻¹ ∧
        (Real.sqrt (1 - J).det)⁻¹ ≤
          Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)))) ∧
      ∀ x : Fin (I + 2) → ℝ,
        (gaussianCovarianceDensity S x).toReal / (gaussianCovarianceDensity K x).toReal =
          (Real.sqrt (1 - J).det)⁻¹ * Real.exp (-(x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x)) / 2) ∧
        0 ≤ x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x) ∧
        x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x) ≤ 2 * ∑ i, e i * (K⁻¹ *ᵥ x) i ^ 2 := by
  obtain ⟨I, hI, hα, hR⟩ := source_gaussian_parameters t A hA ht
  refine ⟨I, hI, ?_⟩
  exact gaussian_disk_fixed_density b (Real.exp 1 * sourceLowerRadius t + 14) A
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (by omega : 0 < I + 1) hA hα
    (by simpa using hR)

/-- Density and event comparisons for one and the same maximal source scale, including
independent auxiliary variables and the conditional-moment lower bound. -/
theorem source_gaussian_density_comparison {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      (let K := brownianTimeMatrix (geometricDiskPointTime R A diskEnergyGapRatio α (I + 1)) (I + 2)
      let e := geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) (I + 1)
      let S := K - Matrix.diagonal e
      let J := diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e
      K.PosDef ∧ S.PosDef ∧
      (1 ≤ (Real.sqrt (1 - J).det)⁻¹ ∧
        (Real.sqrt (1 - J).det)⁻¹ ≤
          Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)))) ∧
      ∀ x : Fin (I + 2) → ℝ,
        (gaussianCovarianceDensity S x).toReal / (gaussianCovarianceDensity K x).toReal =
          (Real.sqrt (1 - J).det)⁻¹ * Real.exp (-(x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x)) / 2) ∧
        0 ≤ x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x) ∧
        x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x) ≤ 2 * ∑ i, e i * (K⁻¹ *ᵥ x) i ^ 2) ∧
      (let K := brownianTimeMatrix (geometricDiskPointTime R A diskEnergyGapRatio α (I + 1)) (I + 2)
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
  refine ⟨I, hI, ?_, ?_⟩
  · exact gaussian_disk_fixed_density b (Real.exp 1 * sourceLowerRadius t + 14) A
      (sourceReferenceIntensity (sourceLowerRadius t) 14) (by omega : 0 < I + 1) hA hα
      (by simpa using hR)
  · exact gaussian_disk_fixed_parameters ν b (Real.exp 1 * sourceLowerRadius t + 14) A
      (sourceReferenceIntensity (sourceLowerRadius t) 14) (by omega : 0 < I + 1) hA hα
      (by simpa using hR)

end SRWTightness
