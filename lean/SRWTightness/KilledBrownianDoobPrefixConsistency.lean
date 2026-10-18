import SRWTightness.KilledBrownianDoobPrefixWeight
import SRWTightness.KilledBrownianDoobTerminalWeight
import SRWTightness.ScaledGaussianPrefixLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Restricting the actual Doob path to an earlier positive time gives its shorter-horizon law. -/
theorem killed_brownian_doob_prefix_consistency (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrT : r < T) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) =
    (killedBrownianDoobCoefficientLaw r x).map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt r * gaussianDyadicPath ω (u / r)) := by
  letI := killed_brownian_doob_probability hReflection T x hT hx
  letI := killed_brownian_doob_probability hReflection r x hr hx
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  let Q := fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt r * gaussianDyadicPath ω (u / r)
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hQ : Measurable Q := measurable_pi_lambda _ (fun _ ↦
    measurable_const.mul (gaussianDyadicPath_measurable _))
  have hLaw : gaussianCoefficientLaw.map P = gaussianCoefficientLaw.map Q :=
    scaled_gaussian_prefix_law T r hT hr hrT.le
  apply Measure.ext
  intro B hB
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((killedBrownianDoobCoefficientLaw T x).map P).real B =
    ((killedBrownianDoobCoefficientLaw r x).map Q).real B
  rw [map_measureReal_apply hP hB, map_measureReal_apply hQ hB]
  have hp := killed_brownian_doob_prefix_weight hReflection T x r hT hx hr hrT B hB
  have hq := killed_brownian_doob_terminal_weight hReflection r x hr hx B hB
  change (killedBrownianDoobCoefficientLaw T x).real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) ∈ B} =
    (killedBrownianDoobCoefficientLaw r x).real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ Real.sqrt r * gaussianDyadicPath ω (u / r)) ∈ B}
  rw [hp, hq]
  let A : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | p ∈ B ∧ p ∈ dyadicFlatPathEvent r x ∧ p ⟨r, hr.le, le_rfl⟩ < x}
  let f := fun p : Set.Icc (0 : ℝ) r → ℝ ↦ (x - p ⟨r, hr.le, le_rfl⟩) / x
  have hA : MeasurableSet A := hB.inter ((dyadicFlatPathEvent_measurable r x).inter
    (measurableSet_lt (measurable_pi_apply _) measurable_const))
  have hf : Measurable f := by dsimp [f]; fun_prop
  change (∫ ω in P ⁻¹' A, f (P ω) ∂gaussianCoefficientLaw) =
    ∫ ω in Q ⁻¹' A, f (Q ω) ∂gaussianCoefficientLaw
  rw [← setIntegral_map hA hf.aestronglyMeasurable hP.aemeasurable,
    ← setIntegral_map hA hf.aestronglyMeasurable hQ.aemeasurable, hLaw]

end SRWTightness
