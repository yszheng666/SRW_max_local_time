import SRWTightness.MatrixRowContraction

namespace SRWTightness

/-- The discrete occupation kernel is G-I, including the diagonal subtraction. -/
theorem observationGreen_sub_one_entry_nonneg (D A : Finset Site) (hAD : A ⊆ D)
    (y z : A) : 0 ≤ killedGreen D y z - (if y = z then 1 else 0) := by
  classical
  by_cases h : y = z
  · subst z
    simp only [ite_true]
    linarith [killedGreen_diag_ge_one D y (hAD y.property)]
  · simp only [if_neg h, sub_zero]
    exact killedGreen_nonneg D y z

/-- The absolute row norm equals the nonnegative discrete row sum used in the manuscript. -/
theorem observationGreen_sub_one_abs_row (D A : Finset Site) (hAD : A ⊆ D) (y : A) :
    (∑ z : A, |killedGreen D y z - (if y = z then 1 else 0)|) =
      ∑ z : A, (killedGreen D y z - (if y = z then 1 else 0)) := by
  apply Finset.sum_congr rfl
  intro z hz
  exact abs_of_nonneg (observationGreen_sub_one_entry_nonneg D A hAD y z)

end SRWTightness
