import SRWTightness.GaussianDensityChange
import SRWTightness.DensityEventLower
import SRWTightness.GaussianDiagonalDensityBounds

open Matrix MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def gaussianInverseCorrection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x)

theorem gaussianCoordinateLaw_isProbabilityMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) : IsProbabilityMeasure (gaussianCoordinateLaw K) := by
  unfold gaussianCoordinateLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem gaussianInverseCorrection_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) : Measurable (gaussianInverseCorrection K S) := by
  unfold gaussianInverseCorrection
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- The lower event comparison for actual Gaussian laws under a conditional correction moment. -/
theorem gaussian_event_lower_of_correction_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (hfactor : 1 ≤ Real.sqrt K.det / Real.sqrt S.det)
    (hn : ∀ x, 0 ≤ gaussianInverseCorrection K S x)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) (C : ℝ)
    (hQ : IntegrableOn (gaussianInverseCorrection K S) s (gaussianCoordinateLaw K))
    (hmean : ∫ x in s, gaussianInverseCorrection K S x ∂gaussianCoordinateLaw K ≤
      C * (gaussianCoordinateLaw K).real s) :
    Real.exp (-C / 2) * (gaussianCoordinateLaw K).real s ≤ (gaussianCoordinateLaw S).real s := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hp : 0 ≤ Real.sqrt K.det / Real.sqrt S.det := le_trans zero_le_one hfactor
  have hu (x : ι → ℝ) : gaussianDensityWeight K S x ≤ Real.sqrt K.det / Real.sqrt S.det := by
    unfold gaussianDensityWeight
    apply mul_le_of_le_one_right hp
    apply Real.exp_le_one_iff.mpr
    have hh := hn x
    change 0 ≤ x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x) at hh
    linarith
  have hl (x : ι → ℝ) : Real.exp (-gaussianInverseCorrection K S x / 2) ≤
      gaussianDensityWeight K S x := by
    have hh := mul_le_mul_of_nonneg_right hfactor
      (Real.exp_nonneg (-gaussianInverseCorrection K S x / 2))
    simpa only [one_mul, gaussianDensityWeight, gaussianInverseCorrection] using hh
  rw [gaussianCoordinateLaw_changeDensity K S hK hS]
  exact density_event_lower_of_moment (gaussianCoordinateLaw K) (gaussianDensityWeight K S)
    (gaussianInverseCorrection K S) C (Real.sqrt K.det / Real.sqrt S.det)
    (gaussianDensityWeight_measurable K S) (gaussianDensityWeight_nonneg K S) hu
    (gaussianInverseCorrection_measurable K S) hn hl s hs hQ hmean

theorem gaussian_diagonal_normalization_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2) :
    1 ≤ Real.sqrt K.det / Real.sqrt (K - Matrix.diagonal e).det := by
  have hd := (smallDiagonal_determinant_bounds K hK c hc hlo e he hesmall).1
  have hJ := smallDiagonal_resolvent_posDef K hK c hc hlo e he hesmall
  have hk : Real.sqrt K.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hK.det_pos)
  have hj : Real.sqrt (1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).det ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hJ.det_pos)
  rw [← diagonalSquareRoot_square e he, covariance_sub_square_det K _ hK.isUnit,
    Real.sqrt_mul hK.det_pos.le]
  have heq : Real.sqrt K.det /
      (Real.sqrt K.det * Real.sqrt (1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).det) =
      (Real.sqrt (1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).det)⁻¹ := by
    field_simp
  rwa [heq]

end SRWTightness
