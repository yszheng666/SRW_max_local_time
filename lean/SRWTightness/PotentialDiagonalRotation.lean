import SRWTightness.PotentialDiagonalTorus

open MeasureTheory
noncomputable section
namespace SRWTightness

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local instance : MeasureSpace Real.Angle :=
  inferInstanceAs (MeasureSpace (AddCircle (2 * Real.pi)))
local instance : BorelSpace Real.Angle :=
  inferInstanceAs (BorelSpace (AddCircle (2 * Real.pi)))
local instance : SecondCountableTopology Real.Angle :=
  inferInstanceAs (SecondCountableTopology (AddCircle (2 * Real.pi)))
local instance : BorelSpace (Real.Angle × Real.Angle) :=
  inferInstanceAs (BorelSpace (AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi)))

/-- The rotated diagonal Fourier integrand separates the two angular coordinates. -/
noncomputable def rotatedDiagonalTorusIntegrand (n : ℕ) (p : Real.Angle × Real.Angle) : ℝ :=
  (1 - Real.Angle.cos (n • (p.1 + p.1))) /
    (1 - Real.Angle.cos p.1 * Real.Angle.cos p.2)

/-- Diagonal rotation gives the separated cosine denominator exactly. -/
theorem diagonalPotentialTorusIntegrand_rotation (n : ℕ) (p : Real.Angle × Real.Angle) :
    diagonalPotentialTorusIntegrand n (diagonalTorusMap (2 * Real.pi) p) =
      rotatedDiagonalTorusIntegrand n p := by
  have hp : (p.1 + p.2) + (p.1 - p.2) = p.1 + p.1 := by abel
  change (1 - Real.Angle.cos (n • ((p.1 + p.2) + (p.1 - p.2)))) /
    (1 - (Real.Angle.cos (p.1 + p.2) + Real.Angle.cos (p.1 - p.2)) / 2) = _
  rw [hp]
  unfold rotatedDiagonalTorusIntegrand
  congr 1
  simp only [sub_eq_add_neg, Real.Angle.cos_add, Real.Angle.cos_neg,
    Real.Angle.sin_neg]
  ring

/-- The diagonal torus integrand is integrable because it lifts to the original Fourier
integrand. -/
theorem integrable_diagonalPotentialTorusIntegrand (n : ℕ) :
    Integrable (diagonalPotentialTorusIntegrand n) := by
  apply (fourierBoxMeasure_to_torus.integrable_comp
    (measurable_diagonalPotentialTorusIntegrand n).aestronglyMeasurable).mp
  change Integrable (fun p : ℝ × ℝ ↦ diagonalPotentialTorusIntegrand n (p.1, p.2))
    fourierBoxMeasure
  simpa only [diagonalPotentialTorusIntegrand_coe] using
    integrable_potentialFourierIntegrand ((n : ℤ), (n : ℤ))

/-- The rotated integrand is integrable despite its removable singular angular points. -/
theorem integrable_rotatedDiagonalTorusIntegrand (n : ℕ) :
    Integrable (rotatedDiagonalTorusIntegrand n) := by
  have h := (diagonalTorusMap_measurePreserving (2 * Real.pi)).integrable_comp_of_integrable
    (integrable_diagonalPotentialTorusIntegrand n)
  simp only [Function.comp_def, diagonalPotentialTorusIntegrand_rotation] at h
  exact h

/-- The original diagonal potential equals the separated rotated torus integral. -/
theorem potentialKernel_diagonal_rotated (n : ℕ) :
    potentialKernel ((n : ℤ), (n : ℤ)) =
      (4 * Real.pi ^ 2)⁻¹ * ∫ p, rotatedDiagonalTorusIntegrand n p := by
  rw [potentialKernel_diagonal_torus]
  have h := diagonalTorusMap_integral (2 * Real.pi)
    (diagonalPotentialTorusIntegrand n) (measurable_diagonalPotentialTorusIntegrand n)
  simp only [diagonalPotentialTorusIntegrand_rotation] at h
  exact congrArg (fun x : ℝ ↦ (4 * Real.pi ^ 2)⁻¹ * x) h.symm

end SRWTightness
