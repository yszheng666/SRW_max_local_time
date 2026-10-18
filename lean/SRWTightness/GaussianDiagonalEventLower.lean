import SRWTightness.GaussianEventAuxiliary

open Matrix MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Lower comparison with independent auxiliary variables for a small diagonal covariance loss.
All measures are actual Gaussian laws; the remaining moment bound is the event-specific input. -/
theorem gaussian_diagonal_event_lower_aux {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β] (ν : Measure β) [IsFiniteMeasure ν]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2)
    (hS : (K - Matrix.diagonal e).PosDef)
    (s : Set ((ι → ℝ) × β)) (hs : MeasurableSet s) (C : ℝ)
    (hmean : ∫ x in s, gaussianInverseCorrection K (K - Matrix.diagonal e) x.1
        ∂(gaussianCoordinateLaw K).prod ν ≤ C * ((gaussianCoordinateLaw K).prod ν).real s) :
    Real.exp (-C / 2) * ((gaussianCoordinateLaw K).prod ν).real s ≤
      ((gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν).real s := by
  have hJ := smallDiagonal_resolvent_posDef K hK c hc hlo e he hesmall
  have hJT := smallDiagonal_resolvent_lower K hK.isUnit c hc hlo e he hesmall
  have hKT : Kᵀ = K := by
    ext i j
    have hh := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) hK.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using hh
  have hn (x : ι → ℝ) : 0 ≤ gaussianInverseCorrection K (K - Matrix.diagonal e) x :=
    (covariance_diagonal_inverse_difference_bounds K e he hK.isUnit hKT hJ hJT x).1
  exact gaussian_event_aux_lower_of_correction_moment ν K (K - Matrix.diagonal e) hK hS
    (gaussian_diagonal_normalization_lower K hK c hc hlo e he hesmall) hn s hs C hmean

theorem gaussian_diagonal_event_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2)
    (hS : (K - Matrix.diagonal e).PosDef)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) (C : ℝ)
    (hmean : ∫ x in s, gaussianInverseCorrection K (K - Matrix.diagonal e) x
        ∂gaussianCoordinateLaw K ≤ C * (gaussianCoordinateLaw K).real s) :
    Real.exp (-C / 2) * (gaussianCoordinateLaw K).real s ≤
      (gaussianCoordinateLaw (K - Matrix.diagonal e)).real s := by
  have hJ := smallDiagonal_resolvent_posDef K hK c hc hlo e he hesmall
  have hJT := smallDiagonal_resolvent_lower K hK.isUnit c hc hlo e he hesmall
  have hKT : Kᵀ = K := by
    ext i j
    have hh := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) hK.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using hh
  have hn (x : ι → ℝ) : 0 ≤ gaussianInverseCorrection K (K - Matrix.diagonal e) x :=
    (covariance_diagonal_inverse_difference_bounds K e he hK.isUnit hKT hJ hJT x).1
  exact gaussian_event_lower_of_correction_moment K (K - Matrix.diagonal e) hK hS
    (gaussian_diagonal_normalization_lower K hK c hc hlo e he hesmall) hn s hs C
    (gaussianInverseCorrection_integrable K (K - Matrix.diagonal e)).integrableOn hmean

end SRWTightness
