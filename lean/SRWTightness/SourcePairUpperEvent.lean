import SRWTightness.SourcePairWindowEvent

open MeasureTheory Filter

namespace SRWTightness

/-- The two high sites and flat prefix with its final average deficit, before splitting windows. -/
def sourcePairUpperEvent (t A : ℝ) (I i : ℕ) (At q f : ℝ) :
    Set ((PairObservationIndex (I - i + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :=
  {p | At ≤ p.1 (.inr false) ∧ At ≤ p.1 (.inr true) ∧
    p.1 (.inl (Fin.last (I - i))) ≤
      2 * sourceObservationTime t A I (I - i + 1) + q - f ∧
    (pairObservationExtension I i p.1, p.2) ∈
      sourceBridgedBarrierEvent t A I (sourceObservationTime t A I (I - i + 1)) (fun _ ↦ q)}

theorem sourcePairUpperEvent_measurable (t A : ℝ) (I i : ℕ) (At q f : ℝ) :
    MeasurableSet (sourcePairUpperEvent t A I i At q f) := by
  simp only [sourcePairUpperEvent, Set.setOf_and]
  exact (measurableSet_le measurable_const (by fun_prop)).inter
    ((measurableSet_le measurable_const (by fun_prop)).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
        ((sourceBridgedBarrierEvent_measurable t A I _ (fun _ ↦ q)).preimage
          (((pairObservationExtension_measurable I i).comp measurable_fst).prodMk measurable_snd))))

/-- The three-index windows cover the entire pair event, including the top deficit boundary. -/
theorem sourcePairUpperEvent_window_cover (t A : ℝ) (I i : ℕ) (At q f : ℝ) :
    sourcePairUpperEvent t A I i At q f ⊆
      ⋃ p : ℕ × ℕ × ℕ, sourcePairWindowEvent t A I i At q f p.1 p.2.1 p.2.2 := by
  intro p hp
  obtain ⟨n, m, l, hw⟩ := pairWindow_cover (Fin.last (I - i)) At
    (2 * sourceObservationTime t A I (I - i + 1) + q - f) p.1 hp.1 hp.2.1 hp.2.2.1
  exact Set.mem_iUnion.mpr ⟨(n, m, l), hw, hp.2.2.2⟩

/-- The unsplit event uses the continuous prefix for almost every independent auxiliary bridge. -/
theorem sourcePairUpperEvent_ae_iff (t A : ℝ) (I i : ℕ) (At q f : ℝ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ x : PairObservationIndex (I - i + 1) → ℝ,
      (x, ω) ∈ sourcePairUpperEvent t A I i At q f ↔
      At ≤ x (.inr false) ∧ At ≤ x (.inr true) ∧
        x (.inl (Fin.last (I - i))) ≤ 2 * sourceObservationTime t A I (I - i + 1) + q - f ∧
        ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I - i + 1) →
          sourceBridgedPath t A I (pairObservationExtension I i x) ω v ≤ q := by
  filter_upwards [sourceBridgedBarrierEvent_ae_iff t A I
    (sourceObservationTime t A I (I - i + 1)) (fun _ ↦ q) continuous_const] with ω hω
  intro x
  exact and_congr_right (fun _ ↦ and_congr_right (fun _ ↦
    and_congr_right (fun _ ↦ hω (pairObservationExtension I i x))))

end SRWTightness
