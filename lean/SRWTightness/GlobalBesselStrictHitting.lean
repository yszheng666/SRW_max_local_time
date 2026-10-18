import SRWTightness.GlobalBesselConstruction
import SRWTightness.BesselStrictHittingExact
import SRWTightness.ContinuousCrossingPathLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The global Bessel construction has the exact finite-horizon strict lower-hitting probability. -/
theorem global_bessel_strict_hitting_finite (hReflection : BridgeReflectionInput)
    (T x b : ℝ) (hT : 0 < T) (hb : 0 < b) (hbx : b < x) :
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualGlobalBesselThree x t ω < b} =
      (b / x) * (1 - (gaussianReal 0 T.toNNReal).real (Set.Icc (-(x - b)) (x - b))) := by
  have he := continuous_crossing_probability_of_path_law
    (independentBridgeLaw (Fin 3)) (independentBridgeLaw (Fin 3))
    (actualGlobalBesselThree x) (actualBesselThree T x)
    (actualGlobalBesselThree_measurable x) (actualBesselThree_measurable T x)
    (actualGlobalBesselThree_continuous x) (actualBesselThree_ae_continuous T x)
    T (fun _ ↦ b) continuous_const (global_bessel_finite_horizon_law T x hT)
  exact he.trans (bessel_strict_hitting_exact hReflection T x b hT hb hbx)

end SRWTightness
