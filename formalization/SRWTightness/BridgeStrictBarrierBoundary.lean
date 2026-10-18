import SRWTightness.StrictBarrierAlmostEverywhere
import SRWTightness.BridgeConditionalProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- For a flat barrier above both endpoints, strict and closed bridge survival
agree almost surely. -/
theorem bridge_strict_barrier_boundary (hReflection : BridgeReflectionInput)
    (T b q : ℝ) (hT : 0 < T) (hq : 0 < q) (hb : b < q) :
    ∀ᵐ ω ∂gaussianCoefficientLaw,
      (∀ t ∈ Set.Icc (0 : ℝ) T, endpointBrownianBridge T b t ω < q) ↔
      ω ∈ bridgeFlatEvent T b q := by
  let a := max 0 b
  let F : ℝ → ℝ := fun p ↦ 1 - Real.exp (-(2 * (a + p) * (a + p - b) / T))
  have ha0 : 0 ≤ a := le_max_left _ _
  have hab : b ≤ a := le_max_right _ _
  have haq : a < q := max_lt hq hb
  have hF : Continuous F := by dsimp [F]; fun_prop
  have he (p : ℝ) :
      {ω | ∀ t : Set.Icc (0 : ℝ) T, endpointBrownianBridge T b t ω - a ≤ p} =
        bridgeFlatEvent T b (a + p) := by
    ext ω
    simp only [Set.mem_setOf_eq, bridgeFlatEvent, Subtype.forall]
    constructor <;> intro h t ht <;> have hh := h t ht <;> linarith
  have hm (p : ℝ) (_hp : 0 < p) : NullMeasurableSet
      {ω | ∀ t : Set.Icc (0 : ℝ) T, endpointBrownianBridge T b t ω - a ≤ p}
      gaussianCoefficientLaw := by
    rw [he]
    exact bridgeFlatEvent_nullMeasurable _ _ _
  have hc (p : ℝ) (hp : 0 < p) :
      gaussianCoefficientLaw.real
        {ω | ∀ t : Set.Icc (0 : ℝ) T, endpointBrownianBridge T b t ω - a ≤ p} =
        F p := by
    rw [he]
    exact hReflection T b (a + p) hT (by linarith) (by linarith)
  have hh := strict_barrier_ae_closed gaussianCoefficientLaw
    (fun t : Set.Icc (0 : ℝ) T ↦ fun ω ↦ endpointBrownianBridge T b t ω - a)
    F (q - a) (sub_pos.mpr haq) hF.continuousAt hm hc
  filter_upwards [hh] with ω hω
  simpa only [Subtype.forall, sub_lt_sub_iff_right, sub_le_sub_iff_right,
    bridgeFlatEvent, Set.mem_setOf_eq] using hω

end SRWTightness
