import SRWTightness.GlobalBesselHittingMeasurable
import SRWTightness.GlobalBesselEscape
import SRWTightness.ContinuousLevelHitting

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Starting below a positive level, the global Bessel process reaches that level almost surely. -/
theorem global_bessel_level_hit_from_below (x b : ℝ)
    (hx : 0 < x) (hb : 0 < b) (hxb : x ≤ b) :
    ∀ᵐ ω ∂independentBridgeLaw (Fin 3),
      ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω = b := by
  filter_upwards [actualGlobalBesselThree_continuous x,
    global_bessel_exceeds_ae x b hx hb] with ω hc hω
  obtain ⟨n, hn⟩ := hω
  apply continuous_level_hit_of_above (fun t ↦ actualGlobalBesselThree x t ω) hc
    b ((n : ℝ) + 1)
  · rw [actualGlobalBesselThree_initial x hx.le]
    exact hxb
  · positivity
  · exact hn.le

/-- The global Bessel process has the literal infinite-time level-hitting probability. -/
theorem global_bessel_level_hitting (hReflection : BridgeReflectionInput)
    (x b : ℝ) (hx : 0 < x) (hb : 0 < b) :
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω = b} = min 1 (b / x) := by
  by_cases hxb : x ≤ b
  · have he : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω = b} =ᵐ[
        independentBridgeLaw (Fin 3)] Set.univ := by
      filter_upwards [global_bessel_level_hit_from_below x b hx hb hxb] with ω hω
      apply propext
      exact ⟨fun _ ↦ trivial, fun _ ↦ hω⟩
    rw [measureReal_congr he, probReal_univ, min_eq_left ((one_le_div hx).mpr hxb)]
  · have he : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω = b} =ᵐ[
        independentBridgeLaw (Fin 3)]
        {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b} := by
      filter_upwards [actualGlobalBesselThree_continuous x] with ω hc
      apply propext
      apply (continuous_lower_hit_iff_level (fun t ↦ actualGlobalBesselThree x t ω) hc b ?_).symm
      rw [actualGlobalBesselThree_initial x hx.le]
      exact (lt_of_not_ge hxb).le
    rw [measureReal_congr he]
    exact global_bessel_infinite_hitting hReflection x b hx hb

/-- The literal infinite-time level-hitting event is completed measurable. -/
theorem global_bessel_level_hitting_nullMeasurable (hReflection : BridgeReflectionInput)
    (x b : ℝ) (hx : 0 < x) (hb : 0 < b) :
    NullMeasurableSet {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω = b}
      (independentBridgeLaw (Fin 3)) := by
  by_cases hxb : x ≤ b
  · have he : (Set.univ : Set (Fin 3 → GaussianCoefficientSpace)) =ᵐ[
        independentBridgeLaw (Fin 3)]
        {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω = b} := by
      filter_upwards [global_bessel_level_hit_from_below x b hx hb hxb] with ω hω
      apply propext
      exact ⟨fun _ ↦ hω, fun _ ↦ trivial⟩
    exact MeasurableSet.univ.nullMeasurableSet.congr he
  · have he : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b} =ᵐ[
        independentBridgeLaw (Fin 3)]
        {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω = b} := by
      filter_upwards [actualGlobalBesselThree_continuous x] with ω hc
      apply propext
      apply continuous_lower_hit_iff_level (fun t ↦ actualGlobalBesselThree x t ω) hc b
      rw [actualGlobalBesselThree_initial x hx.le]
      exact (lt_of_not_ge hxb).le
    exact (global_bessel_hitting_nullMeasurable hReflection x b hx hb).congr he

end SRWTightness
