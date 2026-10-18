import SRWTightness.BridgePrefixGaussianMixture
import SRWTightness.ScaledGaussianCenteredMixture
import SRWTightness.DensityMapPullback

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual whole bridge prefix is the Brownian prefix weighted by the remaining heat kernel. -/
theorem bridge_prefix_heat_kernel_law (T b r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hrT : r < T) :
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω) =
    (gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) r) ↦ Real.sqrt r * gaussianDyadicPath ω (t / r))).withDensity
      (fun p ↦ ENNReal.ofReal (gaussianPDFReal (p ⟨r, hr.le, le_rfl⟩)
        (T - r).toNNReal b / gaussianPDFReal 0 T.toNNReal b)) := by
  let e : Set.Icc (0 : ℝ) r := ⟨r, hr.le, le_rfl⟩
  let Z := fun ω (t : Set.Icc (0 : ℝ) r) ↦ actualIntervalBridge r t ω
  let ν := gaussianCoefficientLaw.map Z
  let μ := (gaussianReal 0 r.toNNReal).prod ν
  let H := fun p : ℝ × (Set.Icc (0 : ℝ) r → ℝ) ↦
    fun t : Set.Icc (0 : ℝ) r ↦ p.2 t + (t : ℝ) / r * p.1
  let ρ := fun p : Set.Icc (0 : ℝ) r → ℝ ↦
    ENNReal.ofReal (gaussianPDFReal (p e) (T - r).toNNReal b / gaussianPDFReal 0 T.toNNReal b)
  have hZ : Measurable Z := measurable_pi_lambda _ (fun t ↦
    actualIntervalBridge_measurable r t)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hρ : Measurable ρ := by dsimp [ρ]; fun_prop
  have hz : ∀ᵐ p ∂ν, p e = 0 := by
    apply (ae_map_iff hZ.aemeasurable
      (measurableSet_eq_fun (measurable_pi_apply e) measurable_const)).mpr
    exact ae_of_all _ (fun ω ↦ actualIntervalBridge_terminal r hr ω)
  have hp : ∀ᵐ p ∂μ, p.2 e = 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun ((measurable_pi_apply e).comp measurable_snd) measurable_const)).mpr
    exact ae_of_all _ (fun _ ↦ hz)
  have hw : (fun p : ℝ × (Set.Icc (0 : ℝ) r → ℝ) ↦
      ENNReal.ofReal (gaussianPDFReal p.1 (T - r).toNNReal b /
        gaussianPDFReal 0 T.toNNReal b)) =ᵐ[μ] fun p ↦ ρ (H p) := by
    filter_upwards [hp] with p hp
    simp only [ρ, H, hp, e, div_self (ne_of_gt hr), one_mul, zero_add]
  rw [bridge_prefix_gaussian_mixture T b r hT hr hrT,
    scaled_gaussian_centered_mixture r hr]
  change (μ.withDensity _).map H = (μ.map H).withDensity ρ
  rw [withDensity_congr_ae hw, density_map_pullback μ H hH ρ hρ]

end SRWTightness
