import SRWTightness.PairObservationExtension
import SRWTightness.PairWindowsCover
import SRWTightness.SourceBridgedConvex

open MeasureTheory Filter

namespace SRWTightness

/-- The exact pair window intersected with the flat bridged prefix, expressed by dyadic tests. -/
def sourcePairWindowEvent (t A : ℝ) (I i : ℕ) (At q f : ℝ) (n m l : ℕ) :
    Set ((PairObservationIndex (I - i + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :=
  {p | p.1 ∈ pairWindow (Fin.last (I - i)) At
      (2 * sourceObservationTime t A I (I - i + 1) + q - f) n m l ∧
    (pairObservationExtension I i p.1, p.2) ∈
      sourceBridgedBarrierEvent t A I (sourceObservationTime t A I (I - i + 1)) (fun _ ↦ q)}

theorem sourcePairWindowEvent_measurable (t A : ℝ) (I i : ℕ)
    (At q f : ℝ) (n m l : ℕ) : MeasurableSet (sourcePairWindowEvent t A I i At q f n m l) := by
  exact ((pairWindow_measurable _ _ _ _ _ _).preimage measurable_fst).inter
    ((sourceBridgedBarrierEvent_measurable t A I
      (sourceObservationTime t A I (I - i + 1)) (fun _ ↦ q)).preimage
      (((pairObservationExtension_measurable I i).comp measurable_fst).prodMk measurable_snd))

theorem sourcePairWindowEvent_convex (t A : ℝ) (I i : ℕ)
    (At q f : ℝ) (n m l : ℕ) (ω : ℕ → GaussianCoefficientSpace) :
    Convex ℝ ((fun x ↦ (x, ω)) ⁻¹' sourcePairWindowEvent t A I i At q f n m l) := by
  exact (pairWindow_convex _ _ _ _ _ _).inter
    ((sourceBridgedBarrierEvent_convex t A I ω
      (sourceObservationTime t A I (I - i + 1)) (fun _ ↦ q)).linear_preimage
      (pairObservationExtension I i))

/-- The countable-test event equals the continuous prefix event for almost every auxiliary bridge. -/
theorem sourcePairWindowEvent_ae_iff (t A : ℝ) (I i : ℕ) (At q f : ℝ) (n m l : ℕ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ x : PairObservationIndex (I - i + 1) → ℝ,
      (x, ω) ∈ sourcePairWindowEvent t A I i At q f n m l ↔
        x ∈ pairWindow (Fin.last (I - i)) At
          (2 * sourceObservationTime t A I (I - i + 1) + q - f) n m l ∧
        ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I - i + 1) →
          sourceBridgedPath t A I (pairObservationExtension I i x) ω v ≤ q := by
  filter_upwards [sourceBridgedBarrierEvent_ae_iff t A I
    (sourceObservationTime t A I (I - i + 1)) (fun _ ↦ q) continuous_const] with ω hω
  intro x
  exact and_congr_right (fun _ ↦ hω (pairObservationExtension I i x))

end SRWTightness
