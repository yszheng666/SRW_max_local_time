import SRWTightness.KilledBrownianDoobBesselPathLaw
import SRWTightness.BesselPrefixLaw
import SRWTightness.DensityMapPullback

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The original weighted Bessel prefix is the same endpoint weighting of the actual Doob path. -/
theorem bessel_bridge_doob_prefix_law (hReflection : BridgeReflectionInput)
    (T x y s : ℝ) (hT : 0 < T) (hx : 0 < x) (hs : 0 < s) (hsT : s < T) :
    ((independentBridgeLaw (Fin 3)).withDensity
      (fun ω ↦ ENNReal.ofReal (besselThreeDensity (T - s) (actualBesselThree T x s ω) y /
        besselThreeDensity T x y))).map
      (fun ω (u : Set.Icc (0 : ℝ) s) ↦ actualBesselThree T x u ω) =
    ((killedBrownianDoobCoefficientLaw s x).withDensity
      (fun ω ↦ ENNReal.ofReal
        (besselThreeDensity (T - s) (x - Real.sqrt s * gaussianDyadicPath ω (s / s)) y /
          besselThreeDensity T x y))).map
      (fun ω (u : Set.Icc (0 : ℝ) s) ↦ x - Real.sqrt s * gaussianDyadicPath ω (u / s)) := by
  let P := fun ω (u : Set.Icc (0 : ℝ) s) ↦ actualBesselThree T x u ω
  let D := fun ω (u : Set.Icc (0 : ℝ) s) ↦
    x - Real.sqrt s * gaussianDyadicPath ω (u / s)
  let e : Set.Icc (0 : ℝ) s := ⟨s, hs.le, le_rfl⟩
  let ρ := fun p : Set.Icc (0 : ℝ) s → ℝ ↦ ENNReal.ofReal
    (besselThreeDensity (T - s) (p e) y / besselThreeDensity T x y)
  have hρ : Measurable ρ := by
    dsimp [ρ]
    unfold besselThreeDensity killedBrownianDensity
    fun_prop
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦
    actualBesselThree_measurable T x _)
  have hD : Measurable D := measurable_pi_lambda _ (fun _ ↦
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _)))
  have he : (independentBridgeLaw (Fin 3)).map P =
      (killedBrownianDoobCoefficientLaw s x).map D :=
    (bessel_radial_prefix_law T x s hT hs hsT.le).trans
      (killed_brownian_doob_bessel_path_law hReflection s x hs hx).symm
  change ((independentBridgeLaw (Fin 3)).withDensity (fun ω ↦ ρ (P ω))).map P =
    ((killedBrownianDoobCoefficientLaw s x).withDensity (fun ω ↦ ρ (D ω))).map D
  rw [density_map_pullback _ P hP ρ hρ, density_map_pullback _ D hD ρ hρ, he]

end SRWTightness
