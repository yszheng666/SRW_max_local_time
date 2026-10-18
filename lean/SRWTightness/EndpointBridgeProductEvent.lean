import SRWTightness.SourceBridgeCurvedProbability
import SRWTightness.SourceBridgedEvent

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A measurable endpoint-window and curved-bridge event on endpoint times coefficient space. -/
def endpointBridgeProductEvent (T l u q d γ : ℝ) : Set (ℝ × GaussianCoefficientSpace) :=
  {p | p.1 ∈ Set.Icc l u ∧ ∀ n j : ℕ, (j : ℝ) / 2 ^ n ≤ T →
    endpointBrownianBridge T p.1 ((j : ℝ) / 2 ^ n) p.2 ≤ q - (d - (j : ℝ) / 2 ^ n) ^ γ}

theorem endpointBridgeProductEvent_measurable (T l u q d γ : ℝ) :
    MeasurableSet (endpointBridgeProductEvent T l u q d γ) := by
  unfold endpointBridgeProductEvent
  simp only [Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter (measurableSet_Icc.preimage measurable_fst)
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  apply measurableSet_le _ measurable_const
  exact ((actualIntervalBridge_measurable T _).comp measurable_snd).add
    (measurable_const.mul measurable_fst)

theorem endpointBridgeProductEvent_subset (T l u q d γ : ℝ) :
    endpointBridgeProductEvent T l u q d γ ⊆ Set.Icc l u ×ˢ Set.univ := by
  intro p hp
  exact ⟨hp.1, Set.mem_univ _⟩

/-- Every section inside the endpoint window has the actual continuous curved-bridge probability. -/
theorem endpointBridgeProductEvent_section (T l u q d γ b : ℝ)
    (hγ : 0 ≤ γ) (hb : b ∈ Set.Icc l u) :
    gaussianCoefficientLaw.real (Prod.mk b ⁻¹' endpointBridgeProductEvent T l u q d γ) =
      gaussianCoefficientLaw.real (bridgeCurvedEvent T b q d γ) := by
  apply measureReal_congr
  filter_upwards [actualIntervalBridge_continuous T] with ω hω
  apply propext
  change (b ∈ Set.Icc l u ∧ ∀ n j : ℕ, (j : ℝ) / 2 ^ n ≤ T →
    endpointBrownianBridge T b ((j : ℝ) / 2 ^ n) ω ≤ q - (d - (j : ℝ) / 2 ^ n) ^ γ) ↔ _
  rw [and_iff_right hb]
  have hc : Continuous (fun v ↦ endpointBrownianBridge T b v ω) :=
    hω.add ((continuous_id.div_const T).mul continuous_const)
  have hbound : Continuous (fun v : ℝ ↦ q - (d - v) ^ γ) :=
    continuous_const.sub ((Real.continuous_rpow_const hγ).comp
      (continuous_const.sub continuous_id))
  have hh := (continuous_barrier_iff_dyadic _ _ hc hbound T).symm
  change _ ↔ ∀ v ∈ Set.Icc (0 : ℝ) T,
    endpointBrownianBridge T b v ω ≤ q - (d - v) ^ γ
  simpa only [Set.mem_Icc, and_imp] using hh

end SRWTightness
