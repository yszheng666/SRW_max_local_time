import SRWTightness.BridgePrefixHeatKernelLaw
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Any measurable prefix integral under the actual bridge has its exact Brownian kernel weight. -/
theorem bridge_prefix_heat_kernel_integral (T b r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hrT : r < T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (f : (Set.Icc (0 : ℝ) r → ℝ) → ℝ) (hf : Measurable f) :
    (∫ ω in {ω | (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ A},
      f (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∂gaussianCoefficientLaw) =
    ∫ ω in {ω | (fun t : Set.Icc (0 : ℝ) r ↦
        Real.sqrt r * gaussianDyadicPath ω (t / r)) ∈ A},
      (gaussianPDFReal (Real.sqrt r * gaussianDyadicPath ω (r / r)) (T - r).toNNReal b /
        gaussianPDFReal 0 T.toNNReal b) *
      f (fun t : Set.Icc (0 : ℝ) r ↦ Real.sqrt r * gaussianDyadicPath ω (t / r))
        ∂gaussianCoefficientLaw := by
  let P := fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω
  let W := fun ω (t : Set.Icc (0 : ℝ) r) ↦
    Real.sqrt r * gaussianDyadicPath ω (t / r)
  let g := fun p : Set.Icc (0 : ℝ) r → ℝ ↦
    gaussianPDFReal (p ⟨r, hr.le, le_rfl⟩) (T - r).toNNReal b /
      gaussianPDFReal 0 T.toNNReal b
  have hP : Measurable P := measurable_pi_lambda _ (fun t ↦
    (actualIntervalBridge_measurable T t).add measurable_const)
  have hW : Measurable W := measurable_pi_lambda _ (fun t ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hgn (p) : 0 ≤ g p := div_nonneg (gaussianPDFReal_nonneg _ _ _)
    (gaussianPDFReal_nonneg _ _ _)
  change (∫ ω in P ⁻¹' A, f (P ω) ∂gaussianCoefficientLaw) =
    ∫ ω in W ⁻¹' A, g (W ω) * f (W ω) ∂gaussianCoefficientLaw
  rw [← setIntegral_map hA hf.aestronglyMeasurable hP.aemeasurable]
  rw [bridge_prefix_heat_kernel_law T b r hT hr hrT]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hg.ennreal_ofReal
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top)) f hA]
  simp only [ENNReal.toReal_ofReal (hgn _), smul_eq_mul]
  exact setIntegral_map hA (hg.mul hf).aestronglyMeasurable hW.aemeasurable

end SRWTightness
