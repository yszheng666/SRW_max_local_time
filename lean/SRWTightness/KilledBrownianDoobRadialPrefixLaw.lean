import SRWTightness.KilledBrownianDoobPrefixConsistency

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Doob distance path has consistent whole-prefix laws, including the full horizon. -/
theorem killed_brownian_doob_radial_prefix_law (hReflection : BridgeReflectionInput)
    (T x r : ℝ) (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrT : r ≤ T) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ x - Real.sqrt T * gaussianDyadicPath ω (u / T)) =
    (killedBrownianDoobCoefficientLaw r x).map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ x - Real.sqrt r * gaussianDyadicPath ω (u / r)) := by
  rcases eq_or_lt_of_le hrT with h | h
  · subst r
    rfl
  · let H := fun p : Set.Icc (0 : ℝ) r → ℝ ↦ fun u ↦ x - p u
    have hH : Measurable H := measurable_pi_lambda _ (fun u ↦
      measurable_const.sub (measurable_pi_apply u))
    have hm (S : ℝ) : Measurable (fun ω (u : Set.Icc (0 : ℝ) r) ↦
        Real.sqrt S * gaussianDyadicPath ω (u / S)) :=
      measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _))
    have he := congrArg (fun μ : Measure (Set.Icc (0 : ℝ) r → ℝ) ↦ μ.map H)
      (killed_brownian_doob_prefix_consistency hReflection T x r hT hx hr h)
    rw [Measure.map_map hH (hm T), Measure.map_map hH (hm r)] at he
    exact he

end SRWTightness
