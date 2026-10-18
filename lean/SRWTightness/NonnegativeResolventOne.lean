import SRWTightness.FiniteResolventRowInternal

open Matrix

namespace SRWTightness

/-- The resolvent of a nonnegative row contraction sends one to a vector at least one. -/
theorem nonnegative_resolvent_one_ge_one (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, |M i j| ≤ q) :
    ∀ i, 1 ≤ ((1 - M)⁻¹.mulVec 1) i := by
  classical
  let v : ι → ℝ := (1 - M)⁻¹.mulVec 1
  have hu := matrix_row_contraction_isUnit ι M q hq hq1 hrow
  have he : (1 - M).mulVec v = 1 := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mulVec]
  have hf (i : ι) : v i = 1 + ∑ j, M i j * v j := by
    have hh := congrFun he i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.one_apply] at hh
    change v i - ∑ j, M i j * v j = 1 at hh
    linarith
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image Finset.univ v ⟨i, Finset.mem_univ i⟩
    have hnon : 0 ≤ v k := by
      by_contra hn
      have hneg : v k < 0 := lt_of_not_ge hn
      have hs : ∑ j, M k j ≤ q := by
        simpa only [abs_of_nonneg (hM k _)] using hrow k
      have hb : 1 + v k * q ≤ v k := by
        calc
          _ ≤ 1 + v k * (∑ j, M k j) :=
            add_le_add_right (mul_le_mul_of_nonpos_left hs hneg.le) 1
          _ = 1 + ∑ j, M k j * v k := by
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ ≤ 1 + ∑ j, M k j * v j := by
            apply add_le_add_right
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hmin j hj) (hM k j)
          _ = v k := (hf k).symm
      nlinarith
    exact hnon.trans (hmin i (Finset.mem_univ i))
  intro i
  change 1 ≤ v i
  rw [hf i]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ ↦ mul_nonneg (hM i j) (hv j)))

end SRWTightness
