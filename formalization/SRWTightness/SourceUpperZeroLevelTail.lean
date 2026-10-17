import SRWTightness.SourceUpperMeshLocalTail
import SRWTightness.SourceUpperMeshWeightSum

open Filter MeasureTheory

namespace SRWTightness

/-- The zero-level mesh tail has the same exponential excess-height cost. -/
theorem source_upper_zero_level_tail (hinput : PotentialKernelAsymptoticInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s →
      (∑ z ∈ sourceUpperMesh t 0, pathLaw.real {ω |
        4 + s ≤ Real.sqrt (2 * (sourceUpperMeshCount t 0 z ω : ℝ))}) ≤
          C * Real.exp (-3 * s / 2) := by
  obtain ⟨K, C₁, hK, hC₁, hlocal⟩ := source_upper_mesh_local_tail hinput
  obtain ⟨C₂, hC₂, hmesh⟩ := source_upper_mesh_weight_sum
  refine ⟨C₁ * C₂ * Real.exp (9 * K / 8), by positivity, ?_⟩
  filter_upwards [hlocal, hmesh] with t hl hm
  intro s hs
  have hweight : (∑ z ∈ sourceUpperMesh t 0, sourceUpperMeshWeight t 0 z) ≤ C₂ := by
    simpa using hm 0 (Nat.zero_le _)
  have hsum := Finset.sum_le_sum (fun z hz ↦ hl 0 (Nat.zero_le _) z hz (4 + s) (by linarith))
  simp only [Nat.cast_zero, zero_add, zero_add, div_one] at hsum
  have he : Real.exp (-(4 + s) ^ 2 / (2 * K)) ≤
      Real.exp (9 * K / 8) * Real.exp (-3 * s / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by linarith : 0 < 2 * K)).mpr
    nlinarith [sq_nonneg (4 + s - 3 * K / 2)]
  calc
    _ ≤ (C₁ * ∑ z ∈ sourceUpperMesh t 0, sourceUpperMeshWeight t 0 z) *
        Real.exp (-(4 + s) ^ 2 / (2 * K)) := by
      simpa only [Finset.sum_mul, Finset.mul_sum] using hsum
    _ ≤ (C₁ * C₂) * Real.exp (-(4 + s) ^ 2 / (2 * K)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hC₁.le)
        (Real.exp_pos _).le
    _ ≤ (C₁ * C₂) * (Real.exp (9 * K / 8) * Real.exp (-3 * s / 2)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end SRWTightness
