import SRWTightness.ObservationGenerating

open Matrix

namespace SRWTightness

noncomputable def laplaceGreenMatrix (D A : Finset Site) (f : A → ℝ) : Matrix A A ℝ :=
  1 + observationGreen D A * Matrix.diagonal f

 theorem laplace_resolvent_factor (D A : Finset Site) (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) :
    observationResolventMatrix D A (fun z ↦ (1 + f z)⁻¹) *
      Matrix.diagonal (fun z ↦ 1 + f z) = laplaceGreenMatrix D A f := by
  ext y z
  have hn : 1 + f z ≠ 0 := by linarith [hf z]
  simp only [Matrix.mul_diagonal, observationResolventMatrix, laplaceGreenMatrix,
    Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · simp only [if_pos hyz]
    field_simp
    ring
  · simp only [if_neg hyz]
    field_simp
    ring

 theorem laplaceGreenMatrix_isUnit (D A : Finset Site) (hAD : A ⊆ D)
    (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) : IsUnit (laplaceGreenMatrix D A f) := by
  rw [← laplace_resolvent_factor D A f hf]
  apply IsUnit.mul
  · apply observationResolventMatrix_isUnit D A hAD
    · intro z
      exact inv_nonneg.mpr (by linarith [hf z])
    · intro z
      exact inv_le_one_of_one_le₀ (by linarith [hf z])
  · apply Matrix.isUnit_diagonal.mpr
    apply Pi.isUnit_iff.mpr
    intro z
    exact isUnit_iff_ne_zero.mpr (by linarith [hf z])

end SRWTightness
