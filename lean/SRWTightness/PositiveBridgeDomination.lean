import SRWTightness.ExternalPositiveBridge
import SRWTightness.BesselBridgeDensityBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem actualBesselThree_measurable (T x t : ℝ) : Measurable (actualBesselThree T x t) := by
  unfold actualBesselThree
  apply Real.continuous_sqrt.measurable.comp
  exact Finset.measurable_sum _ (fun i _ ↦
    (measurable_const.add (measurable_const.mul
      ((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i)))).pow_const 2)

theorem actualBesselThree_path_measurable (T x s : ℝ) :
    Measurable (fun ω (t : Set.Icc (0 : ℝ) s) ↦ actualBesselThree T x t ω) :=
  measurable_pi_iff.mpr (fun t ↦ actualBesselThree_measurable T x t)

/-- Internal half-path domination from the exact external restriction identity and kernel estimates. -/
theorem positiveBridge_path_domination (hBridge : PositiveBridgeRestrictionInput)
    (hPositive : BesselThreePositiveInput) (T x y s M : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (hsT : s ≤ T / 2)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    (positiveBridgeCoefficientLaw T x y).map
      (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y t ω) ≤
    ENNReal.ofReal (8 * Real.exp M) • (independentBridgeLaw (Fin 3)).map
      (fun ω (t : Set.Icc (0 : ℝ) s) ↦ actualBesselThree T x t ω) := by
  have hslt : s < T := by linarith
  rw [hBridge T x y s hT hx hy hs hslt]
  have hμ : (independentBridgeLaw (Fin 3)).withDensity
      (fun ω ↦ ENNReal.ofReal (besselThreeDensity (T - s) (actualBesselThree T x s ω) y /
        besselThreeDensity T x y)) ≤
      ENNReal.ofReal (8 * Real.exp M) • independentBridgeLaw (Fin 3) := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hPositive T x s hT hx hs hslt.le] with ω hω
    exact ENNReal.ofReal_le_ofReal (besselThree_bridge_density_bound T (T - s) x y
      (actualBesselThree T x s ω) M hT (by linarith) (by linarith) hx hy hω hxy hM)
  have hm := Measure.map_mono hμ (actualBesselThree_path_measurable T x s)
  simpa only [Measure.map_smul] using hm

end SRWTightness
