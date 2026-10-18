import SRWTightness.KilledBrownianDoobBridgeDensity
import SRWTightness.PositiveBridgeKilledPrefixProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Positive bridge prefix events equal the exact bridge weighting of actual Doob prefix events. -/
theorem positive_bridge_doob_prefix_probability (hReflection : BridgeReflectionInput)
    (T x y s : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (hsT : s < T)
    (B : Set (Set.Icc (0 : ℝ) s → ℝ)) (hB : MeasurableSet B) :
    (positiveBridgeCoefficientLaw T x y).real {ω |
      (fun u : Set.Icc (0 : ℝ) s ↦ positiveEndpointBridge T x y u ω) ∈ B} =
    ((killedBrownianDoobCoefficientLaw s x).withDensity
      (fun ω ↦ ENNReal.ofReal
        (besselThreeDensity (T - s) (x - Real.sqrt s * gaussianDyadicPath ω (s / s)) y /
          besselThreeDensity T x y))).real {ω |
      (fun u : Set.Icc (0 : ℝ) s ↦ x - Real.sqrt s * gaussianDyadicPath ω (u / s)) ∈ B} := by
  let D := fun ω (u : Set.Icc (0 : ℝ) s) ↦
    x - Real.sqrt s * gaussianDyadicPath ω (u / s)
  let S := {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
    0 < x - Real.sqrt s * gaussianDyadicPath ω (t / s)}
  let w := fun ω ↦
    killedBrownianDensity (T - s) (x - Real.sqrt s * gaussianDyadicPath ω (s / s)) y /
      killedBrownianDensity T x y
  have hD : Measurable D := measurable_pi_lambda _ (fun _ ↦
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _)))
  have hw : Measurable w := by
    dsimp [w]
    unfold killedBrownianDensity
    have hm := gaussianDyadicPath_measurable (s / s)
    fun_prop
  have hn (ω) (hω : ω ∈ S) : 0 ≤ w ω :=
    (div_pos (killedBrownianDensity_pos (T - s) _ y (sub_pos.mpr hsT)
      (hω s ⟨hs.le, le_rfl⟩) hy) (killedBrownianDensity_pos T x y hT hx hy)).le
  rw [positive_bridge_killed_prefix_probability hReflection T x y s hT hx hy hs hsT B hB,
    killed_brownian_doob_bridge_density hReflection T x y s hT hx hy hs hsT]
  change (∫ ω in {ω | D ω ∈ B ∧ ω ∈ S}, w ω ∂gaussianCoefficientLaw) =
    ((gaussianCoefficientLaw.restrict S).withDensity (fun ω ↦ ENNReal.ofReal (w ω))).real
      (D ⁻¹' B)
  rw [restricted_density_event_real gaussianCoefficientLaw S
    (scaled_gaussian_strict_survival_nullMeasurable hReflection s x hs hx)
    w hw hn (D ⁻¹' B) (hB.preimage hD)]
  apply setIntegral_congr_set
  exact ae_of_all _ (fun ω ↦ by
    apply propext
    change (D ω ∈ B ∧ ω ∈ S) ↔ (ω ∈ S ∧ D ω ∈ B)
    tauto)

end SRWTightness
