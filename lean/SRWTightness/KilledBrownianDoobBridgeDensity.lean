import SRWTightness.KilledBrownianDoobEventReal
import SRWTightness.DoobBridgeKernelCancellation

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Weighting the actual Doob path by the Bessel bridge ratio leaves the killed bridge density. -/
theorem killed_brownian_doob_bridge_density (hReflection : BridgeReflectionInput)
    (T x y s : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y)
    (hs : 0 < s) (hsT : s < T) :
    (killedBrownianDoobCoefficientLaw s x).withDensity
      (fun ω ↦ ENNReal.ofReal
        (besselThreeDensity (T - s) (x - Real.sqrt s * gaussianDyadicPath ω (s / s)) y /
          besselThreeDensity T x y)) =
    (gaussianCoefficientLaw.restrict
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
        0 < x - Real.sqrt s * gaussianDyadicPath ω (t / s)}).withDensity
      (fun ω ↦ ENNReal.ofReal
        (killedBrownianDensity (T - s) (x - Real.sqrt s * gaussianDyadicPath ω (s / s)) y /
          killedBrownianDensity T x y)) := by
  let S := {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
    0 < x - Real.sqrt s * gaussianDyadicPath ω (t / s)}
  let R := fun ω ↦ x - Real.sqrt s * gaussianDyadicPath ω (s / s)
  have hR : Measurable R :=
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _))
  have hw : Measurable (fun ω ↦ ENNReal.ofReal (R ω / x)) := (hR.div_const x).ennreal_ofReal
  have hρ : Measurable (fun ω ↦ ENNReal.ofReal
      (besselThreeDensity (T - s) (R ω) y / besselThreeDensity T x y)) := by
    unfold besselThreeDensity killedBrownianDensity
    fun_prop
  change ((gaussianCoefficientLaw.restrict S).withDensity
    (fun ω ↦ ENNReal.ofReal (R ω / x))).withDensity
      (fun ω ↦ ENNReal.ofReal
        (besselThreeDensity (T - s) (R ω) y / besselThreeDensity T x y)) = _
  rw [← withDensity_mul _ hw hρ]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem₀
    (scaled_gaussian_strict_survival_nullMeasurable hReflection s x hs hx)] with ω hω
  have hz : 0 < R ω := hω s ⟨hs.le, le_rfl⟩
  change ENNReal.ofReal (R ω / x) * ENNReal.ofReal
    (besselThreeDensity (T - s) (R ω) y / besselThreeDensity T x y) = _
  rw [← ENNReal.ofReal_mul (div_nonneg hz.le hx.le),
    doob_bridge_kernel_cancellation T s x y (R ω) hx.ne' hy.ne' hz.ne']

end SRWTightness
