import SRWTightness.SourceBridgedPath

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

/-- All nonnegative dyadic tests that lie before the final average time. -/
def sourceBridgedBarrierEvent (t A : ℝ) (I : ℕ) (V : ℝ) (bound : ℝ → ℝ) :
    Set ((Fin ((I + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :=
  {p | ∀ n j : ℕ, (j : ℝ) / 2 ^ n ≤ V →
    sourceBridgedPath t A I p.1 p.2 ((j : ℝ) / 2 ^ n) ≤ bound ((j : ℝ) / 2 ^ n)}

theorem sourceBridgedBarrierEvent_measurable (t A : ℝ) (I : ℕ) (V : ℝ)
    (bound : ℝ → ℝ) : MeasurableSet (sourceBridgedBarrierEvent t A I V bound) := by
  simp only [sourceBridgedBarrierEvent, Set.setOf_forall]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun j ↦
    MeasurableSet.iInter fun _ ↦ measurableSet_le
      (sourceBridgedPath_joint_measurable t A I _) measurable_const

theorem continuous_barrier_iff_dyadic (f bound : ℝ → ℝ) (hf : Continuous f)
    (hb : Continuous bound) (V : ℝ) :
    (∀ v : ℝ, 0 ≤ v → v ≤ V → f v ≤ bound v) ↔
      (∀ n j : ℕ, (j : ℝ) / 2 ^ n ≤ V → f ((j : ℝ) / 2 ^ n) ≤ bound ((j : ℝ) / 2 ^ n)) := by
  constructor
  · intro h n j hj
    exact h _ (by positivity) hj
  · intro h v hv hvV
    apply le_of_tendsto_of_tendsto ((hf.tendsto v).comp (dyadicTime_tendsto v hv))
      ((hb.tendsto v).comp (dyadicTime_tendsto v hv))
    exact Eventually.of_forall fun n ↦ h n (dyadicTimeIndex n v)
      ((dyadicTime_bounds n v hv).2.1.trans hvV)

theorem sourceBridgedBarrierEvent_ae_iff (t A : ℝ) (I : ℕ) (V : ℝ)
    (bound : ℝ → ℝ) (hb : Continuous bound) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ x : Fin ((I + 1) + 1) → ℝ,
      (x, ω) ∈ sourceBridgedBarrierEvent t A I V bound ↔
        ∀ v : ℝ, 0 ≤ v → v ≤ V → sourceBridgedPath t A I x ω v ≤ bound v := by
  filter_upwards [sourceBridgedPath_ae_continuous t A I] with ω hω
  intro x
  exact (continuous_barrier_iff_dyadic _ _ (hω x) hb V).symm

theorem sourceBridgedBarrierEvent_ae_rpow (t A : ℝ) (I : ℕ) (V q d γ : ℝ)
    (hγ : 0 ≤ γ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ x : Fin ((I + 1) + 1) → ℝ,
      (x, ω) ∈ sourceBridgedBarrierEvent t A I V (fun v ↦ q - (d - v) ^ γ) ↔
        ∀ v : ℝ, 0 ≤ v → v ≤ V → sourceBridgedPath t A I x ω v ≤ q - (d - v) ^ γ := by
  apply sourceBridgedBarrierEvent_ae_iff
  exact continuous_const.sub
    ((Real.continuous_rpow_const hγ).comp (continuous_const.sub continuous_id))

end SRWTightness
