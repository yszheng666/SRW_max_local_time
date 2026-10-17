import SRWTightness.ExternalBrownianReconstruction
import SRWTightness.FiniteGaussianPathReconstruction

open MeasureTheory ProbabilityTheory

namespace SRWTightness

set_option maxHeartbeats 800000 in
/-- The exact finite retained mesh meets reconstruction hypotheses for arbitrary strict gaps. -/
theorem finiteGaussian_endpoint_bridge_law (hReconstruct : BrownianBridgeReconstructionInput)
    (T : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hT : T 0 = 0)
    (hgap : ∀ j < n, T j < T (j + 1)) :
    ((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ)).map
      (fun p ↦ (finiteGaussianBridgedPath T n n p.1 p.2 (T n),
        fun v : Set.Icc (0 : ℝ) (T n) ↦ finiteGaussianBridgedPath T n n p.1 p.2 v)) =
      ((gaussianReal 0 (T n).toNNReal).prod gaussianCoefficientLaw).map
        (fun p ↦ (p.1, fun v : Set.Icc (0 : ℝ) (T n) ↦
          endpointBrownianBridge (T n) p.1 v p.2)) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T n)
  have hg := hgap
  have hpos : 0 < T n := by
    have h01 := hgap 0 (by omega)
    have h1n := timeGridTime_mono T n hgap (by omega : 1 ≤ n) le_rfl
    simp only [hT, zero_add] at h01
    linarith
  apply hReconstruct ((Fin n → ℝ) × (ℕ → GaussianCoefficientSpace))
    ((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod (independentBridgeLaw ℕ))
    (fun v p ↦ finiteGaussianBridgedPath T n n p.1 p.2 v) (T n) hpos
    (finiteGaussianBridgedPath_gaussian T n hg)
  · intro v hv hvT
    exact finiteGaussianBridgedPath_mean T n hn hg v (by simpa only [hT] using hv) hvT
  · intro s t hs hsT ht htT
    exact finiteGaussianBridgedPath_covariance T n hn hT hgap s t hs hsT ht htT

end SRWTightness
