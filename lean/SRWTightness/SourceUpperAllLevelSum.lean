import SRWTightness.SourceUpperZeroLevelTail
import SRWTightness.SourceUpperActualBarrierSum
import SRWTightness.SourceUpperCurvatureSum

open Filter MeasureTheory

namespace SRWTightness

/-- The actual mesh crossing probabilities summed over all coarse levels, including zero. -/
theorem source_upper_all_level_sum (hinput : PotentialKernelAsymptoticInput)
    (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      (∑ j ∈ Finset.range (sourceUpperCoarseDepth t + 1),
        ∑ z ∈ sourceUpperMesh t j, pathLaw.real {ω |
          sourceUpperBarrier t s j ≤
            Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ))}) ≤
              C * Real.exp (-3 * s / 2) := by
  obtain ⟨C₀, hC₀, hzero⟩ := source_upper_zero_level_tail hinput
  obtain ⟨C₁, hC₁, hlocal⟩ := source_upper_actual_barrier_sum hinput hScale
  obtain ⟨C₂, hC₂, hcurve⟩ := source_upper_curvature_sum hScale
  obtain ⟨B, _, hcond⟩ := source_upper_threshold_conditions hScale
  refine ⟨(C₀ + C₁) * C₂, by positivity, ?_⟩
  filter_upwards [hzero, hlocal, hcurve, hcond] with t hz hl hc ht
  intro s hs hslog
  let f := fun j : ℕ ↦ ((j : ℝ) + 1) ^ 3 *
    Real.exp (-(3 / 2 : ℝ) * sourceUpperBarrierCurvature t j)
  have hT : 0 ≤ sourceUpperTotalDepth t := by
    have h := ht.2.2.2.1
    linarith [ht.1]
  have hw0 : sourceUpperBarrierCurvature t 0 = 0 := by
    simp [sourceUpperBarrierCurvature, min_eq_left hT]
  have hb0 : sourceUpperBarrier t s 0 = 4 + s := by
    simp [sourceUpperBarrier, hw0]
  have hpoint : ∀ j ∈ Finset.range (sourceUpperCoarseDepth t + 1),
      (∑ z ∈ sourceUpperMesh t j, pathLaw.real {ω | sourceUpperBarrier t s j ≤
        Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ))}) ≤
          ((C₀ + C₁) * Real.exp (-3 * s / 2)) * f j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      have h := hz s hs
      rw [hb0]
      simp only [f, Nat.cast_zero, zero_add, one_pow, hw0, mul_zero, Real.exp_zero,
        mul_one]
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
    · have hj1 : 1 ≤ j := by omega
      have hjN : j ≤ sourceUpperCoarseDepth t := by
        have h := Finset.mem_range.mp hj
        omega
      have h := hl s hs hslog j hj1 hjN 0 le_rfl
      simp only [add_zero] at h
      have he : Real.exp (-3 * (4 + s + sourceUpperBarrierCurvature t j) / 2) ≤
          Real.exp (-3 * s / 2) *
            Real.exp (-(3 / 2 : ℝ) * sourceUpperBarrierCurvature t j) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      calc
        _ ≤ C₁ * ((j : ℝ) + 1) ^ 3 *
            Real.exp (-3 * (4 + s + sourceUpperBarrierCurvature t j) / 2) := h
        _ ≤ C₁ * ((j : ℝ) + 1) ^ 3 * (Real.exp (-3 * s / 2) *
            Real.exp (-(3 / 2 : ℝ) * sourceUpperBarrierCurvature t j)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = (C₁ * Real.exp (-3 * s / 2)) * f j := by dsimp [f]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le) (by
            dsimp [f]
            positivity)
  calc
    _ ≤ ∑ j ∈ Finset.range (sourceUpperCoarseDepth t + 1),
        ((C₀ + C₁) * Real.exp (-3 * s / 2)) * f j := Finset.sum_le_sum hpoint
    _ = ((C₀ + C₁) * Real.exp (-3 * s / 2)) *
        ∑ j ∈ Finset.range (sourceUpperCoarseDepth t + 1), f j := by rw [Finset.mul_sum]
    _ ≤ ((C₀ + C₁) * Real.exp (-3 * s / 2)) * C₂ :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end SRWTightness
