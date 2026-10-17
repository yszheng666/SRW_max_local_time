import SRWTightness.PotentialDiagonalRotation

open MeasureTheory
noncomputable section
namespace SRWTightness

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local instance : MeasureSpace Real.Angle :=
  inferInstanceAs (MeasureSpace (AddCircle (2 * Real.pi)))
local instance : IsFiniteMeasure (volume : Measure Real.Angle) :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure (AddCircle (2 * Real.pi))))
local instance : BorelSpace Real.Angle :=
  inferInstanceAs (BorelSpace (AddCircle (2 * Real.pi)))
local instance : SecondCountableTopology Real.Angle :=
  inferInstanceAs (SecondCountableTopology (AddCircle (2 * Real.pi)))
local instance : BorelSpace (Real.Angle × Real.Angle) :=
  inferInstanceAs (BorelSpace (AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi)))

/-- The rotated Haar integral equals an iterated full-period real integral. -/
theorem rotated_diagonal_iterated_integral (n : ℕ) :
    (∫ p, rotatedDiagonalTorusIntegrand n p) =
      ∫ u in 0..2 * Real.pi, ∫ v in 0..2 * Real.pi,
        (1 - Real.cos (2 * (n : ℝ) * u)) / (1 - Real.cos u * Real.cos v) := by
  refine (integral_prod (μ := (volume : Measure Real.Angle))
    (ν := (volume : Measure Real.Angle)) (rotatedDiagonalTorusIntegrand n)
    (integrable_rotatedDiagonalTorusIntegrand n)).trans ?_
  have ho := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
    (fun u : Real.Angle ↦ ∫ v : Real.Angle, rotatedDiagonalTorusIntegrand n (u, v))
  simp only [zero_add] at ho
  refine ho.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro u hu
  have hi := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
    (fun v : Real.Angle ↦ rotatedDiagonalTorusIntegrand n ((u : Real.Angle), v))
  simp only [zero_add] at hi
  refine hi.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro v hv
  unfold rotatedDiagonalTorusIntegrand
  simp only [← Real.Angle.coe_add, ← Real.Angle.coe_nsmul, Real.Angle.cos_coe, nsmul_eq_mul]
  congr 2
  ring

end SRWTightness
