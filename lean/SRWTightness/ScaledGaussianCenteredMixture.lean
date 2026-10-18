import SRWTightness.ScaledGaussianPathLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual scaled Brownian path is the Gaussian endpoint/centered bridge mixture. -/
theorem scaled_gaussian_centered_mixture (r : ℝ) (hr : 0 < r) :
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) r) ↦ Real.sqrt r * gaussianDyadicPath ω (t / r)) =
    ((gaussianReal 0 r.toNNReal).prod
      (gaussianCoefficientLaw.map
        (fun ω (t : Set.Icc (0 : ℝ) r) ↦ actualIntervalBridge r t ω))).map
      (fun p (t : Set.Icc (0 : ℝ) r) ↦ p.2 t + (t : ℝ) / r * p.1) := by
  let Z := fun ω (t : Set.Icc (0 : ℝ) r) ↦ actualIntervalBridge r t ω
  let H := fun p : ℝ × (Set.Icc (0 : ℝ) r → ℝ) ↦
    fun t : Set.Icc (0 : ℝ) r ↦ p.2 t + (t : ℝ) / r * p.1
  have hZ : Measurable Z := measurable_pi_lambda _ (fun t ↦
    actualIntervalBridge_measurable r t)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hp : (gaussianReal 0 r.toNNReal).prod (gaussianCoefficientLaw.map Z) =
      ((gaussianReal 0 r.toNNReal).prod gaussianCoefficientLaw).map
        (Prod.map id Z) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map (gaussianReal 0 r.toNNReal) gaussianCoefficientLaw measurable_id hZ
  have he := congrArg
    (fun μ : Measure (ℝ × (Set.Icc (0 : ℝ) r → ℝ)) ↦ μ.map Prod.snd)
    (scaled_gaussian_endpoint_bridge_law r hr)
  have hleft : Measurable (fun ω ↦ (Real.sqrt r * gaussianDyadicPath ω (r / r),
      fun t : Set.Icc (0 : ℝ) r ↦ Real.sqrt r * gaussianDyadicPath ω (t / r))) := by
    exact (measurable_const.mul (gaussianDyadicPath_measurable _)).prodMk
      (measurable_pi_lambda _ (fun t ↦
        measurable_const.mul (gaussianDyadicPath_measurable _)))
  have hright : Measurable (fun p : ℝ × GaussianCoefficientSpace ↦
      (p.1, fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge r p.1 t p.2)) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro t
    exact ((actualIntervalBridge_measurable r t).comp measurable_snd).add
      (measurable_const.mul measurable_fst)
  rw [Measure.map_map measurable_snd hleft, Measure.map_map measurable_snd hright] at he
  change _ = ((gaussianReal 0 r.toNNReal).prod (gaussianCoefficientLaw.map Z)).map H
  rw [hp, Measure.map_map hH (measurable_id.prodMap hZ)]
  exact he

end SRWTightness
