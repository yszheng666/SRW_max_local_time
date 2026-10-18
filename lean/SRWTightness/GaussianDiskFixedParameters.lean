import SRWTightness.GaussianDiskPointComparison
import SRWTightness.DiskPointParameterChoice

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Universal geometric ratio and inner-radius threshold give comparison for the complete
average-plus-center Gaussian vector, uniformly in the number of scales. -/
theorem gaussian_disk_fixed_parameters {n : ℕ} {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (b : Site) (R A α : ℝ) (hn : 0 < n)
    (hA : diskPointGaussianMinimumRadius ≤ A) (hα : α ≤ 2 * (2 / Real.pi))
    (hR : diskEnergyOuterRatio * (A * diskEnergyGapRatio ^ (n - 1)) ≤ R) :
    let K := brownianTimeMatrix (geometricDiskPointTime R A diskEnergyGapRatio α n) (n + 1)
    let e := geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) n
    (K - Matrix.diagonal e).PosDef ∧
    (gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν ≤
      ENNReal.ofReal (Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)))) •
        ((gaussianCoordinateLaw K).prod ν) ∧
    ∀ (s : Set (((Fin (n + 1)) → ℝ) × β)), MeasurableSet s → ∀ C : ℝ,
      (∫ x in s, gaussianInverseCorrection K (K - Matrix.diagonal e) x.1
        ∂(gaussianCoordinateLaw K).prod ν ≤ C * ((gaussianCoordinateLaw K).prod ν).real s) →
      Real.exp (-C / 2) * ((gaussianCoordinateLaw K).prod ν).real s ≤
        ((gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν).real s := by
  have hbase := diskPointGaussianMinimumRadius_ge_base.trans hA
  obtain ⟨ha, hq, hsep, houter, htime, _⟩ := diskGaussianParameterChoice A R α n hbase hα hR
  have hp : 1 ≤ diskEnergyGapRatio ^ (n - 1) := one_le_pow₀ (by linarith)
  have harad : 1 ≤ A * diskEnergyGapRatio ^ (n - 1) := by nlinarith
  have hfirst := equilibriumEnergyTime_disk_ge_one R _ α harad houter htime
  exact gaussian_disk_point_comparison ν b R A diskEnergyGapRatio α hn ha hq
    diskEnergyGapRatio_log_lower hsep hfirst
    (diskPointGaussianMinimumRadius_log_gap A hA)
    (diskPointGaussianMinimumRadius_small_error A hA)

end SRWTightness
