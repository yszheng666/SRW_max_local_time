import SRWTightness.ObservationGreen

open Matrix

namespace SRWTightness

/-- Strict absolute row-sum contraction gives a finite resolvent without a spectral assumption. -/
theorem matrix_one_sub_isUnit_of_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i, ∑ j, |M i j| < 1) : IsUnit (1 - M) := by
  have hker (u : ι → ℝ) (hu : (1 - M).mulVec u = 0) : u = 0 := by
    by_contra hn
    have hex : ∃ j, u j ≠ 0 := by
      by_contra! hh
      apply hn
      funext j
      exact hh j
    obtain ⟨j, hj⟩ := hex
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun k ↦ |u k|)
      ⟨j, Finset.mem_univ j⟩
    have hp : 0 < |u i| := (abs_pos.mpr hj).trans_le (hmax j (Finset.mem_univ j))
    have he := congrFun hu i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply] at he
    have heq : u i = ∑ j, M i j * u j := sub_eq_zero.mp he
    have hab : |u i| ≤ ∑ j, |M i j| * |u j| := by
      rw [heq]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j ↦ M i j * u j) Finset.univ
    have hb : (∑ j, |M i j| * |u j|) ≤ (∑ j, |M i j|) * |u i| := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hmax j hj) (abs_nonneg _)
    have hc : (∑ j, |M i j|) * |u i| < |u i| := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right (hM i) hp
    exact (not_lt_of_ge (hab.trans hb)) hc
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hz : (1 - M).mulVec (u - v) = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  exact sub_eq_zero.mp (hker (u - v) hz)

 theorem observationResolvent_isUnit_of_row_sum (D A : Finset Site) (v : A → ℝ)
    (hrow : ∀ y : A, ∑ z : A,
      |killedGreen D y z - (if y = z then 1 else 0)| * |v z - 1| < 1) :
    IsUnit (observationResolventMatrix D A v) := by
  apply matrix_one_sub_isUnit_of_row_sum
  intro y
  simpa only [Matrix.mul_diagonal, observationGreen, Matrix.sub_apply, Matrix.one_apply,
    abs_mul] using hrow y

end SRWTightness
