import SRWTightness.ScaledGaussianStrictFlatProbability
import SRWTightness.BesselInverseGaussianInterval

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The exact inverse moment equals actual Brownian survival, using the original
reflection input. -/
theorem bessel_inverse_brownian_survival (hReflection : BridgeReflectionInput)
    (T x s : ℝ) (hT : 0 < T) (hx : 0 < x) (hs : 0 < s) (hsT : s ≤ T) :
    (∫ ω, (actualBesselThree T x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) =
      x⁻¹ * gaussianCoefficientLaw.real
        {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
          0 < x - Real.sqrt s * gaussianDyadicPath ω (t / s)} := by
  rw [bessel_inverse_gaussian_interval T x s hT hx hs hsT,
    ← scaled_gaussian_strict_flat_probability hReflection s x hs hx]
  simp only [sub_pos]

end SRWTightness
