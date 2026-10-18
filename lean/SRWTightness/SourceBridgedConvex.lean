import SRWTightness.SourceBridgedEvent

namespace SRWTightness

theorem timeGridInterpolation_linear_combination (T x y : ℕ → ℝ) (n : ℕ)
    (a b v : ℝ) :
    timeGridInterpolation T (fun j ↦ a * x j + b * y j) n v =
      a * timeGridInterpolation T x n v + b * timeGridInterpolation T y n v := by
  unfold timeGridInterpolation
  have hs : (∑ j ∈ Finset.range n, timeGridRamp (T j) (T (j + 1)) v *
      (a * x (j + 1) + b * y (j + 1) - (a * x j + b * y j))) =
      ∑ j ∈ Finset.range n,
        (a * (timeGridRamp (T j) (T (j + 1)) v * (x (j + 1) - x j)) +
         b * (timeGridRamp (T j) (T (j + 1)) v * (y (j + 1) - y j))) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

set_option maxHeartbeats 800000 in
theorem sourceAveragePath_affine (t A : ℝ) (I : ℕ)
    (x y : Fin ((I + 1) + 1) → ℝ) (a b v : ℝ) (hab : a + b = 1) :
    sourceAveragePath t A I (a • x + b • y) v =
      a * sourceAveragePath t A I x v + b * sourceAveragePath t A I y v := by
  let c := fun i : Fin ((I + 1) + 1) ↦ 2 * sourceObservationTime t A I (i.val + 1)
  have hm : observationMeshValue (a • x + b • y - c) =
      fun j ↦ a * observationMeshValue (x - c) j + b * observationMeshValue (y - c) j := by
    funext j
    simp only [observationMeshValue]
    split
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [congrArg (fun r : ℝ ↦ r * c ⟨j - 1, by omega⟩) hab]
    · ring
  change timeGridInterpolation (sourceObservationTime t A I)
      (observationMeshValue (a • x + b • y - c)) (I + 1) v =
    a * timeGridInterpolation (sourceObservationTime t A I) (observationMeshValue (x - c)) (I + 1) v +
    b * timeGridInterpolation (sourceObservationTime t A I) (observationMeshValue (y - c)) (I + 1) v
  rw [hm, timeGridInterpolation_linear_combination]

theorem sourceBridgedPath_affine (t A : ℝ) (I : ℕ)
    (x y : Fin ((I + 1) + 1) → ℝ) (ω : ℕ → GaussianCoefficientSpace)
    (a b v : ℝ) (hab : a + b = 1) :
    sourceBridgedPath t A I (a • x + b • y) ω v =
      a * sourceBridgedPath t A I x ω v + b * sourceBridgedPath t A I y ω v := by
  unfold sourceBridgedPath
  rw [sourceAveragePath_affine t A I x y a b v hab]
  nlinarith [congrArg (fun r : ℝ ↦ r * timeGridBridge (sourceObservationTime t A I) (I + 1) ω v) hab]

theorem sourceBridgedPath_barrier_convex (t A : ℝ) (I : ℕ)
    (ω : ℕ → GaussianCoefficientSpace) (D : Set ℝ) (bound : ℝ → ℝ) :
    Convex ℝ {x : Fin ((I + 1) + 1) → ℝ |
      ∀ v ∈ D, sourceBridgedPath t A I x ω v ≤ bound v} := by
  intro x hx y hy a b ha hb hab v hv
  rw [sourceBridgedPath_affine t A I x y ω a b v hab]
  calc
    a * sourceBridgedPath t A I x ω v + b * sourceBridgedPath t A I y ω v ≤
        a * bound v + b * bound v :=
      add_le_add (mul_le_mul_of_nonneg_left (hx v hv) ha)
        (mul_le_mul_of_nonneg_left (hy v hv) hb)
    _ = bound v := by rw [← add_mul, hab, one_mul]

theorem sourceBridgedTestEvent_convex (t A : ℝ) (I : ℕ)
    (ω : ℕ → GaussianCoefficientSpace) (τ bound : ℕ → ℝ) :
    Convex ℝ {x : Fin ((I + 1) + 1) → ℝ |
      (x, ω) ∈ sourceBridgedTestEvent t A I τ bound} := by
  intro x hx y hy a b ha hb hab k
  change sourceBridgedPath t A I (a • x + b • y) ω (τ k) ≤ bound k
  rw [sourceBridgedPath_affine t A I x y ω a b (τ k) hab]
  calc
    a * sourceBridgedPath t A I x ω (τ k) + b * sourceBridgedPath t A I y ω (τ k) ≤
        a * bound k + b * bound k :=
      add_le_add (mul_le_mul_of_nonneg_left (hx k) ha)
        (mul_le_mul_of_nonneg_left (hy k) hb)
    _ = bound k := by rw [← add_mul, hab, one_mul]

theorem sourceBridgedBarrierEvent_convex (t A : ℝ) (I : ℕ)
    (ω : ℕ → GaussianCoefficientSpace) (V : ℝ) (bound : ℝ → ℝ) :
    Convex ℝ {x : Fin ((I + 1) + 1) → ℝ |
      (x, ω) ∈ sourceBridgedBarrierEvent t A I V bound} := by
  intro x hx y hy a b ha hb hab n j hj
  change sourceBridgedPath t A I (a • x + b • y) ω ((j : ℝ) / 2 ^ n) ≤ _
  rw [sourceBridgedPath_affine t A I x y ω a b _ hab]
  calc
    _ ≤ a * bound ((j : ℝ) / 2 ^ n) + b * bound ((j : ℝ) / 2 ^ n) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx n j hj) ha)
        (mul_le_mul_of_nonneg_left (hy n j hj) hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

end SRWTightness
