import SRWTightness.ObservationGreenRowNonnegative

namespace SRWTightness

/-- Maximum row sum of the two-site discrete occupation kernel G-I. -/
noncomputable def twoSiteDiscreteRowMax (D : Finset Site) (z w : Site) : ℝ :=
  max (killedGreen D z z + killedGreen D z w - 1)
    (killedGreen D w z + killedGreen D w w - 1)

/-- The two-site row sum includes exactly one diagonal subtraction. -/
theorem two_site_discrete_row_sum (D : Finset Site) (z w : Site) (hzw : z ≠ w)
    (v : ({z, w} : Finset Site)) :
    (∑ x : ({z, w} : Finset Site),
      (killedGreen D v x - (if v = x then 1 else 0))) =
      killedGreen D v z + killedGreen D v w - 1 := by
  classical
  rw [Finset.sum_sub_distrib]
  have hd : (∑ x : ({z, w} : Finset Site), if v = x then (1 : ℝ) else 0) = 1 := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hd, Finset.sum_coe_sort]
  simp [hzw]

/-- Every row of the actual two-site observation set is bounded by the displayed maximum. -/
theorem two_site_discrete_row_le (D : Finset Site) (z w : Site) (hzw : z ≠ w)
    (v : ({z, w} : Finset Site)) :
    (∑ x : ({z, w} : Finset Site),
      (killedGreen D v x - (if v = x then 1 else 0))) ≤ twoSiteDiscreteRowMax D z w := by
  classical
  rw [two_site_discrete_row_sum D z w hzw v]
  have hv : (v : Site) = z ∨ (v : Site) = w := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using v.property
  rcases hv with hv | hv
  · simp only [hv]
    exact le_max_left _ _
  · simp only [hv]
    exact le_max_right _ _

/-- The actual maximum row sum is nonnegative whenever the first site lies in the killing domain. -/
theorem twoSiteDiscreteRowMax_nonneg (D : Finset Site) (z w : Site) (hz : z ∈ D) :
    0 ≤ twoSiteDiscreteRowMax D z w := by
  have hd := killedGreen_diag_ge_one D z hz
  have ho := killedGreen_nonneg D z w
  exact (show 0 ≤ killedGreen D z z + killedGreen D z w - 1 by linarith).trans
    (le_max_left _ _)

end SRWTightness
