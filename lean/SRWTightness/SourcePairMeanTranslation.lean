import SRWTightness.SourceBridgedConvex
import SRWTightness.PairObservationExtension

namespace SRWTightness

/-- Interpolate centered pair Gaussian coordinates and add the same independent bridges. -/
noncomputable def pairCenteredBridgedPath (t A : ℝ) (I i : ℕ)
    (x : PairObservationIndex (I - i + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace)
    (v : ℝ) : ℝ :=
  timeGridInterpolation (sourceObservationTime t A I)
    (observationMeshValue (pairObservationExtension I i x)) (I + 1) v +
      timeGridBridge (sourceObservationTime t A I) (I + 1) ω v

/-- Mean translation separates the centered interpolation from the deterministic drift correction. -/
theorem sourceBridgedPath_mean_add (t A : ℝ) (I : ℕ)
    (m x : Fin ((I + 1) + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace) (v : ℝ) :
    sourceBridgedPath t A I (m + x) ω v =
      (timeGridInterpolation (sourceObservationTime t A I) (observationMeshValue x) (I + 1) v +
        timeGridBridge (sourceObservationTime t A I) (I + 1) ω v) +
      sourceAveragePath t A I m v := by
  let c := fun j : Fin ((I + 1) + 1) ↦ 2 * sourceObservationTime t A I (j.val + 1)
  have hm : observationMeshValue (m + x - c) =
      fun j ↦ 1 * observationMeshValue x j + 1 * observationMeshValue (m - c) j := by
    funext j
    by_cases h : 0 < j ∧ j ≤ I + 1
    · simp only [observationMeshValue, dif_pos h, Pi.sub_apply, Pi.add_apply]
      ring
    · simp only [observationMeshValue, dif_neg h, mul_zero, add_zero]
  change timeGridInterpolation (sourceObservationTime t A I)
      (observationMeshValue (m + x - c)) (I + 1) v +
        timeGridBridge (sourceObservationTime t A I) (I + 1) ω v =
    (timeGridInterpolation (sourceObservationTime t A I) (observationMeshValue x) (I + 1) v +
      timeGridBridge (sourceObservationTime t A I) (I + 1) ω v) +
      timeGridInterpolation (sourceObservationTime t A I) (observationMeshValue (m - c)) (I + 1) v
  rw [hm, timeGridInterpolation_linear_combination]
  ring

theorem pairCenteredBridgedPath_mean_add (t A : ℝ) (I i : ℕ)
    (m x : PairObservationIndex (I - i + 1) → ℝ)
    (ω : ℕ → GaussianCoefficientSpace) (v : ℝ) :
    sourceBridgedPath t A I (pairObservationExtension I i (m + x)) ω v =
      pairCenteredBridgedPath t A I i x ω v +
        sourceAveragePath t A I (pairObservationExtension I i m) v := by
  rw [map_add]
  exact sourceBridgedPath_mean_add t A I _ _ ω v

/-- Removing a nonnegative mean correction enlarges the flat-prefix event. -/
theorem pairCenteredBridgedPath_barrier_of_shift (t A : ℝ) (I i : ℕ)
    (m x : PairObservationIndex (I - i + 1) → ℝ)
    (ω : ℕ → GaussianCoefficientSpace) (v q : ℝ)
    (hm : 0 ≤ sourceAveragePath t A I (pairObservationExtension I i m) v)
    (hp : sourceBridgedPath t A I (pairObservationExtension I i (m + x)) ω v ≤ q) :
    pairCenteredBridgedPath t A I i x ω v ≤ q := by
  rw [pairCenteredBridgedPath_mean_add] at hp
  linarith

end SRWTightness
