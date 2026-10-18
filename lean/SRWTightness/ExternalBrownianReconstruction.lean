import SRWTightness.GaussianGridPath
import SRWTightness.ExternalBridgeReflection

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Standard Brownian endpoint/bridge disintegration as an exact joint path law. -/
def BrownianBridgeReconstructionInput : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → ℝ) (T : ℝ), 0 < T → IsGaussianProcess X μ →
    (∀ t : ℝ, 0 ≤ t → t ≤ T → (∫ ω, X t ω ∂μ) = 0) →
    (∀ s t : ℝ, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → cov[X s, X t; μ] = min s t) →
    μ.map (fun ω ↦ (X T ω, fun t : Set.Icc (0 : ℝ) T ↦ X t ω)) =
      ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).map
        (fun p ↦ (p.1, fun t : Set.Icc (0 : ℝ) T ↦ endpointBrownianBridge T p.1 t p.2))

/-- The actual interpolated Gaussian grid satisfies every hypothesis of standard reconstruction. -/
theorem gaussianGrid_endpoint_bridge_law (hReconstruct : BrownianBridgeReconstructionInput)
    (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod (independentBridgeLaw ℕ)).map
      (fun p ↦ (gaussianGridPath T n p (T n),
        fun v : Set.Icc (0 : ℝ) (T n) ↦ gaussianGridPath T n p v)) =
      ((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).map
        (fun p ↦ (p.1, fun v : Set.Icc (0 : ℝ) (T n) ↦
          endpointBrownianBridge (T n) p.1 v p.2)) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T (n + 1))
  have hg : ∀ j < n, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  have hpos : 0 < T n := by
    have h01 := hgap 0 (by omega)
    have h1n := timeGridTime_mono T (n + 1)
      (fun j hj ↦ by linarith [hgap j hj]) (by omega : 1 ≤ n) (by omega)
    simp only [hT, zero_add] at h01
    linarith
  apply hReconstruct _ _ (fun v p ↦ gaussianGridPath T n p v) (T n) hpos
    (gaussianGridPath_gaussian T n hg)
  · intro v hv hvT
    exact gaussianGridPath_mean T n hn hg v (by simpa only [hT] using hv) hvT
  · intro s t hs hsT ht htT
    exact gaussianGridPath_covariance T n hn hT hgap s t hs hsT ht htT

end SRWTightness
