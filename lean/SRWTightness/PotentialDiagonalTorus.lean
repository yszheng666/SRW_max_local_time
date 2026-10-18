import SRWTightness.PotentialFourierLaw
import SRWTightness.DiagonalTorusMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

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

/-- The diagonal potential integrand viewed as a function on the angular torus. -/
noncomputable def diagonalPotentialTorusIntegrand (n : ℕ) (p : Real.Angle × Real.Angle) : ℝ :=
  (1 - Real.Angle.cos (n • (p.1 + p.2))) /
    (1 - (Real.Angle.cos p.1 + Real.Angle.cos p.2) / 2)

/-- The torus integrand is measurable, including at its removable zero denominator. -/
theorem measurable_diagonalPotentialTorusIntegrand (n : ℕ) :
    Measurable (diagonalPotentialTorusIntegrand n) := by
  unfold diagonalPotentialTorusIntegrand
  have hc : Measurable Real.Angle.cos := Real.Angle.continuous_cos.measurable
  have ha : Continuous (fun p : Real.Angle × Real.Angle ↦ n • (p.1 + p.2)) := by fun_prop
  exact (measurable_const.sub (hc.comp ha.measurable)).div
    (measurable_const.sub (((hc.comp measurable_fst).add
      (hc.comp measurable_snd)).div_const 2))

/-- Lifting the torus integrand to real angles recovers the original Fourier integrand. -/
theorem diagonalPotentialTorusIntegrand_coe (n : ℕ) (u v : ℝ) :
    diagonalPotentialTorusIntegrand n (u, v) =
      potentialFourierIntegrand ((n : ℤ), (n : ℤ)) (u, v) := by
  unfold diagonalPotentialTorusIntegrand potentialFourierIntegrand fourierPhase fourierDenominator
  simp only [← Real.Angle.coe_add, ← Real.Angle.coe_nsmul, Real.Angle.cos_coe,
    nsmul_eq_mul, Int.cast_natCast]
  congr 2
  ring

/-- Reduction modulo two pi preserves the original interval measure exactly. -/
theorem fourierIntervalMeasure_to_angle :
    MeasurePreserving (fun u : ℝ ↦ (u : Real.Angle)) fourierIntervalMeasure volume := by
  have h := AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [he, Measure.restrict_congr_set Ioc_ae_eq_Icc] at h
  exact h

/-- The complete Fourier box pushes forward to the angular torus Haar measure. -/
theorem fourierBoxMeasure_to_torus :
    MeasurePreserving (fun p : ℝ × ℝ ↦ ((p.1 : Real.Angle), (p.2 : Real.Angle)))
      fourierBoxMeasure volume := by
  exact fourierIntervalMeasure_to_angle.prod fourierIntervalMeasure_to_angle

/-- The actual diagonal potential is exactly its torus integral with the original normalization. -/
theorem potentialKernel_diagonal_torus (n : ℕ) :
    potentialKernel ((n : ℤ), (n : ℤ)) =
      (4 * Real.pi ^ 2)⁻¹ * ∫ p, diagonalPotentialTorusIntegrand n p := by
  have hp := fourierBoxMeasure_to_torus
  have hi := integral_map (μ := fourierBoxMeasure) hp.measurable.aemeasurable
    (measurable_diagonalPotentialTorusIntegrand n).aestronglyMeasurable
  rw [hp.map_eq] at hi
  unfold potentialKernel
  congr 1
  rw [hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p ↦ (diagonalPotentialTorusIntegrand_coe n p.1 p.2).symm)

end SRWTightness
