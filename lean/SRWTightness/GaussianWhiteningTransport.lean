import SRWTightness.GaussianAffineTransport

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace SRWTightness

/-- The covariance square root exactly reconstructs a vector from its centered whitening. -/
theorem gaussian_whitening_reconstruct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m x : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    m + (CFC.sqrt K) *ᵥ ((CFC.sqrt K)⁻¹ *ᵥ (x - m)) = x := by
  have hunit : IsUnit (CFC.sqrt K).det :=
    isUnit_iff_ne_zero.mpr (matrix_sqrt_posDef K hK).det_pos.ne'
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  abel

/-- Reconstruction holds for the actual pushforward law of any measurable vector. -/
theorem whitened_law_reconstruction {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (ρ : Measure Ω) (F : Ω → ι → ℝ) (hF : Measurable F)
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    (ρ.map (fun ω ↦ (CFC.sqrt K)⁻¹ *ᵥ (F ω - m))).map
      (fun x ↦ m + (CFC.sqrt K) *ᵥ x) = ρ.map F := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ω
  exact gaussian_whitening_reconstruct m (F ω) K hK

/-- A convex comparison for a whitened vector gives the corresponding unstandardized Gaussian comparison. -/
theorem convex_gaussian_whitening_comparison {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (ρ : Measure Ω) (F : Ω → ι → ℝ) (hF : Measurable F)
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) (δ : ℝ)
    (happrox : ∀ s : Set (ι → ℝ), MeasurableSet s → Convex ℝ s →
      |(ρ.map (fun ω ↦ (CFC.sqrt K)⁻¹ *ᵥ (F ω - m))).real s -
        (gaussianCoordinateLaw (1 : Matrix ι ι ℝ)).real s| ≤ δ)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) (hc : Convex ℝ s) :
    |(ρ.map F).real s - (gaussianMeanCoordinateLaw m K).real s| ≤ δ := by
  have hh := convex_gaussian_affine_comparison
    (ρ.map (fun ω ↦ (CFC.sqrt K)⁻¹ *ᵥ (F ω - m))) δ happrox m K s hs hc
  rwa [whitened_law_reconstruction ρ F hF m K hK] at hh

/-- Whitened convex comparison also controls events with almost surely convex auxiliary sections. -/
theorem convex_gaussian_whitening_comparison_aux {Ω ι Ξ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ξ]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (F : Ω → ι → ℝ) (hF : Measurable F)
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) (δ : ℝ)
    (happrox : ∀ s : Set (ι → ℝ), MeasurableSet s → Convex ℝ s →
      |(ρ.map (fun ω ↦ (CFC.sqrt K)⁻¹ *ᵥ (F ω - m))).real s -
        (gaussianCoordinateLaw (1 : Matrix ι ι ℝ)).real s| ≤ δ)
    (s : Set ((ι → ℝ) × Ξ)) (hs : MeasurableSet s)
    (hc : ∀ᵐ y ∂ν, Convex ℝ ((fun x ↦ (x, y)) ⁻¹' s)) :
    |((ρ.map F).prod ν).real s - ((gaussianMeanCoordinateLaw m K).prod ν).real s| ≤ δ := by
  letI : IsProbabilityMeasure (ρ.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  letI := gaussianMeanCoordinateLaw_isProbabilityMeasure m K
  exact convex_event_comparison_aux (ρ.map F) (gaussianMeanCoordinateLaw m K) ν δ
    (convex_gaussian_whitening_comparison ρ F hF m K hK δ happrox) s hs hc

end SRWTightness
