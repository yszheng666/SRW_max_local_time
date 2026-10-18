import SRWTightness.FiniteGaussianFlatTransfer
import SRWTightness.FlatBridgeProductIntegral

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The complete original finite Gaussian kernel follows from the existing reconstruction
and reflection inputs; it need not be an additional independent assumption. -/
theorem finite_gaussian_bridge_kernel_from_reconstruction_reflection
    (hReconstruct : BrownianBridgeReconstructionInput) (hReflection : BridgeReflectionInput) :
    FiniteGaussianBridgeKernelInput := by
  intro T n M last hlast hnM hT hgap q a b hq hab hbq
  have hn : 0 < n := by omega
  have hpos : 0 < T n := by
    have h01 := hgap 0 (by omega)
    have h1n := timeGridTime_mono T M hgap (by omega : 1 ≤ n) hnM
    simp only [hT, zero_add] at h01
    linarith
  change ((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ)).real
    (finiteGaussianPrefixWindow T n M last q a b) = _
  rw [finiteGaussian_flat_probability hReconstruct T n M last hlast hnM hT hgap q a b]
  exact flat_bridge_product_integral hReflection (T n) q a b hpos hq hab hbq

end SRWTightness
