import SRWTightness.GaussianDiagonalEventLower
import SRWTightness.SmallDiagonalCovariancePositive

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Complete Gaussian event comparison from quantitative matrix hypotheses.
Applications must still establish these hypotheses for their actual covariance and weights. -/
theorem gaussian_smallDiagonal_event_comparison {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β] (ν : Measure β) [IsFiniteMeasure ν]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2) :
    (K - Matrix.diagonal e).PosDef ∧
    (gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν ≤
      ENNReal.ofReal (Real.exp ((∑ i, e i) / c)) • ((gaussianCoordinateLaw K).prod ν) ∧
    ∀ (s : Set ((ι → ℝ) × β)), MeasurableSet s → ∀ C : ℝ,
      (∫ x in s, gaussianInverseCorrection K (K - Matrix.diagonal e) x.1
        ∂(gaussianCoordinateLaw K).prod ν ≤ C * ((gaussianCoordinateLaw K).prod ν).real s) →
      Real.exp (-C / 2) * ((gaussianCoordinateLaw K).prod ν).real s ≤
        ((gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν).real s := by
  have hS := smallDiagonal_covariance_posDef K hK.isHermitian c hc hlo e hesmall
  refine ⟨hS, gaussian_diagonal_measure_upper_aux ν K hK c hc hlo e he hesmall hS, ?_⟩
  intro s hs C hmean
  exact gaussian_diagonal_event_lower_aux ν K hK c hc hlo e he hesmall hS s hs C hmean

end SRWTightness
