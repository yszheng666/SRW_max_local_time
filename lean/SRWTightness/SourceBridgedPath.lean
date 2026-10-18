import SRWTightness.SourceAveragePath
import SRWTightness.LocalizedIntervalBridge

open MeasureTheory

namespace SRWTightness

noncomputable def sourceBridgedPath (t A : ℝ) (I : ℕ)
    (x : Fin ((I + 1) + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace) (v : ℝ) : ℝ :=
  sourceAveragePath t A I x v + timeGridBridge (sourceObservationTime t A I) (I + 1) ω v

theorem sourceBridgedPath_node (t A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : sourceGaussianThreshold A ≤ t) (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : Fin ((I + 1) + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace) (i : Fin (I + 1)) :
    sourceBridgedPath t A I x ω (sourceObservationTime t A I (i.val + 1)) =
      x i.castSucc - 2 * sourceObservationTime t A I (i.val + 1) := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  unfold sourceBridgedPath
  rw [timeGridBridge_node _ _ _ (fun j hj ↦ by linarith [hg j (by omega)]) (by omega),
    add_zero, sourceAveragePath_node t A hA ht I hI]

theorem sourceBridgedPath_zero (t A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : sourceGaussianThreshold A ≤ t) (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (x : Fin ((I + 1) + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace) :
    sourceBridgedPath t A I x ω 0 = 0 := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hz := timeGridBridge_node (sourceObservationTime t A I) (I + 1) 0
    (fun j hj ↦ by linarith [hg j (by omega)]) (by omega) ω
  rw [sourceObservationTime_zero] at hz
  simp only [sourceBridgedPath, hz, sourceAveragePath_zero t A hA ht I hI, add_zero]

theorem sourceBridgedPath_ae_continuous (t A : ℝ) (I : ℕ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ x : Fin ((I + 1) + 1) → ℝ,
      Continuous (sourceBridgedPath t A I x ω) := by
  filter_upwards [timeGridBridge_ae_continuous (sourceObservationTime t A I) (I + 1)] with ω hω
  intro x
  exact (sourceAveragePath t A I x).continuous.add hω

theorem sourceBridgedPath_measurable (t A : ℝ) (I : ℕ)
    (x : Fin ((I + 1) + 1) → ℝ) (v : ℝ) :
    Measurable (fun ω ↦ sourceBridgedPath t A I x ω v) :=
  measurable_const.add (timeGridBridge_measurable _ _ _)

theorem sourceBridgedPath_ae_barrier_at_node (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ (x : Fin ((I + 1) + 1) → ℝ) (q d γ : ℝ),
      (∀ v : ℝ, 0 ≤ v → v ≤ sourceEquilibriumTime b (sourceLowerRadius t) A 14 →
        sourceBridgedPath t A I x ω v ≤ q - (d - v) ^ γ) →
      ∀ i : Fin (I + 1), x i.castSucc ≤ 2 * sourceObservationTime t A I (i.val + 1) +
        q - (d - sourceObservationTime t A I (i.val + 1)) ^ γ := by
  filter_upwards [timeGridBridge_ae_continuous (sourceObservationTime t A I) (I + 1)] with ω hω
  intro x q d γ hbar i
  have hg := sourceObservationTime_gaps t A hA ht I hI
  exact sourceAveragePath_barrier_at_node b t A hA ht I hI x
    ⟨timeGridBridge (sourceObservationTime t A I) (I + 1) ω, hω⟩ q d γ
    (fun i ↦ timeGridBridge_node _ _ _ (fun j hj ↦ by linarith [hg j (by omega)]) (by omega) ω)
    hbar i

set_option maxHeartbeats 800000 in
theorem sourceAveragePath_continuous_observation (t A : ℝ) (I : ℕ) (v : ℝ) :
    Continuous (fun x : Fin ((I + 1) + 1) → ℝ ↦ sourceAveragePath t A I x v) := by
  have hm : ∀ j : ℕ, Continuous (fun x : Fin ((I + 1) + 1) → ℝ ↦
      observationMeshValue
        (x - fun i ↦ 2 * sourceObservationTime t A I (i.val + 1)) j) := by
    intro j
    unfold observationMeshValue
    split
    · exact (continuous_apply _).sub continuous_const
    · exact continuous_const
  change Continuous (fun x ↦ timeGridInterpolation _
    (observationMeshValue (x - fun i ↦ 2 * sourceObservationTime t A I (i.val + 1))) _ v)
  unfold timeGridInterpolation
  exact (hm 0).add (continuous_finsetSum _ fun j _ ↦
    continuous_const.mul ((hm (j + 1)).sub (hm j)))

theorem sourceBridgedPath_joint_measurable (t A : ℝ) (I : ℕ) (v : ℝ) :
    Measurable (fun p : (Fin ((I + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦
      sourceBridgedPath t A I p.1 p.2 v) :=
  ((sourceAveragePath_continuous_observation t A I v).measurable.comp measurable_fst).add
    ((timeGridBridge_measurable _ _ v).comp measurable_snd)

/-- Countable barrier tests on a prescribed time family. -/
def sourceBridgedTestEvent (t A : ℝ) (I : ℕ) (τ bound : ℕ → ℝ) :
    Set ((Fin ((I + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :=
  {p | ∀ k, sourceBridgedPath t A I p.1 p.2 (τ k) ≤ bound k}

theorem sourceBridgedTestEvent_measurable (t A : ℝ) (I : ℕ) (τ bound : ℕ → ℝ) :
    MeasurableSet (sourceBridgedTestEvent t A I τ bound) := by
  simp only [sourceBridgedTestEvent, Set.setOf_forall]
  exact MeasurableSet.iInter fun k ↦ measurableSet_le
    (sourceBridgedPath_joint_measurable t A I (τ k)) measurable_const

end SRWTightness
