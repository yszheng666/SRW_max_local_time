import SRWTightness.AnnulusEscapeProduct
import SRWTightness.EquilibriumProbability

namespace SRWTightness

/-- The actual exit-before-return equilibrium measure satisfies a boundary escape bound. -/
theorem equilibriumMeasure_disk_boundary_upper (a R : ℝ) (ha : 4 ≤ a)
    (hRa : 2 * a ≤ R) (x : Site) :
    equilibriumMeasure (diskFinset R) (diskFinset a) x ≤
      (diskGreenEnergyConstant / ((2 / Real.pi) * Real.log (R / a))) * (16 / (3 * a)) := by
  have ha0 : 0 < a := by linarith
  have hKD : diskFinset a ⊆ diskFinset R := by
    intro y hy
    simp only [mem_diskFinset, disk, Set.mem_setOf_eq] at hy ⊢
    nlinarith
  let B := (diskGreenEnergyConstant / ((2 / Real.pi) * Real.log (R / a))) * (16 / (3 * a))
  have hlog : 0 < Real.log (R / a) :=
    Real.log_pos ((one_lt_div ha0).mpr (by linarith))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (div_nonneg diskGreenEnergyConstant_pos.le
      (mul_nonneg (by positivity) hlog.le)) (by positivity)
  rw [equilibriumMeasure_eq_charge _ _ hKD, equilibriumCharge]
  by_cases hx : x ∈ diskFinset a
  · rw [if_pos hx]
    have hd (d : Direction) : 1 - setHitProbability (diskFinset R) (diskFinset a)
        (x + step d) ≤ B := by
      by_cases hy : x + step d ∈ diskFinset a
      · simpa only [setHitProbability_one _ _ _ (hKD hy) hy, sub_self] using hB
      · rw [← annulusOuterExitProbability_eq_one_sub_hit]
        apply annulusOuterExitProbability_boundary_upper a R ha hRa
        · simpa only [mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hy
        · apply normSq_step_le x d ha0.le
          exact (show normSq x < a ^ 2 from (mem_diskFinset a x).mp hx).le
    have hs := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset Direction)) ↦ hd d)
    rw [Finset.sum_sub_distrib] at hs
    simp only [Finset.sum_const, Finset.card_univ, Direction, Fintype.card_fin,
      nsmul_eq_mul] at hs
    norm_num at hs
    change 1 - (1 / 4 : ℝ) * _ ≤ B
    linarith
  · rw [if_neg hx]
    exact hB

end SRWTightness
