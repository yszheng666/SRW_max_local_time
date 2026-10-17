import SRWTightness.EndpointBridgePrefixReconstruction
import SRWTightness.GaussianBridgeMiddleDensityLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The whole bridge prefix is an endpoint/short-bridge mixture
with the exact heat-kernel weight. -/
theorem bridge_prefix_gaussian_mixture (T b r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hrT : r < T) :
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω) =
    (((gaussianReal 0 r.toNNReal).prod
      (gaussianCoefficientLaw.map
        (fun ω (t : Set.Icc (0 : ℝ) r) ↦ actualIntervalBridge r t ω))).withDensity
          (fun p ↦ ENNReal.ofReal (gaussianPDFReal p.1 (T - r).toNNReal b /
            gaussianPDFReal 0 T.toNNReal b))).map
              (fun p (t : Set.Icc (0 : ℝ) r) ↦ p.2 t + (t : ℝ) / r * p.1) := by
  rw [endpoint_bridge_prefix_reconstruction T b r hT hr hrT.le,
    gaussian_bridge_middle_density_law T r b hr hrT,
    prod_withDensity_left (by fun_prop)]

end SRWTightness
