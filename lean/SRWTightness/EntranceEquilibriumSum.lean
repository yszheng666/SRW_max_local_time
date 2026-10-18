import SRWTightness.EntranceAtomGreen
import SRWTightness.EquilibriumProbability
import SRWTightness.DirectionReversal

namespace SRWTightness

/-- The lattice last-step sum is the average over the four reversed neighbors. -/
theorem last_step_weight_sum (E : Finset Site) (f : Site → ℝ)
    (hf : ∀ y, y ∉ E → f y = 0) (v : Site) :
    (∑ y ∈ E, f y * ((1 / 4 : ℝ) *
      ∑ d : Direction, if y + step d = v then 1 else 0)) =
      (1 / 4 : ℝ) * ∑ d : Direction, f (v + step d) := by
  classical
  have hh (d : Direction) :
      (∑ y ∈ E, f y * (if y + step d = v then 1 else 0)) = f (v - step d) := by
    simp_rw [← eq_sub_iff_add_eq, mul_ite, mul_one, mul_zero]
    by_cases h : v - step d ∈ E
    · simp [h]
    · simp [h, hf _ h]
  calc
    _ = (1 / 4 : ℝ) * ∑ y ∈ E, ∑ d : Direction,
        f y * (if y + step d = v then 1 else 0) := by
      simp only [Finset.mul_sum, mul_assoc, mul_left_comm]
    _ = (1 / 4 : ℝ) * ∑ d : Direction, ∑ y ∈ E,
        f y * (if y + step d = v then 1 else 0) := by rw [Finset.sum_comm]
    _ = (1 / 4 : ℝ) * ∑ d : Direction, f (v - step d) := by simp_rw [hh]
    _ = _ := by
      congr 1
      apply Fintype.sum_equiv directionReversal
      intro d
      change f (v - step d) = f (v + step (reverseDirection d))
      rw [step_reverseDirection, sub_eq_add_neg]

/-- Escape weights in the last-step entrance sum give the actual equilibrium measure. -/
theorem equilibrium_last_step_sum (D K : Finset Site) (hKD : K ⊆ D)
    (v : Site) (hv : v ∈ K) (hnear : ∀ d : Direction, v + step d ∈ D) :
    (∑ y ∈ D \ K, (1 - setHitProbability D K y) *
      ((1 / 4 : ℝ) * ∑ d : Direction, if y + step d = v then 1 else 0)) =
      equilibriumMeasure D K v := by
  classical
  let f : Site → ℝ := fun y ↦ if y ∈ D \ K then 1 - setHitProbability D K y else 0
  have hf : ∀ y, y ∉ D \ K → f y = 0 := by intro y hy; simp only [f, if_neg hy]
  have hh := last_step_weight_sum (D \ K) f hf v
  have he (y : Site) (hy : y ∈ D \ K) : f y = 1 - setHitProbability D K y := by
    simp only [f, if_pos hy]
  have hn (d : Direction) : f (v + step d) = 1 - setHitProbability D K (v + step d) := by
    by_cases hk : v + step d ∈ K
    · simp [f, hk, setHitProbability_one D K _ (hnear d) hk]
    · simp [f, hk, hnear d]
  rw [equilibriumMeasure_eq_charge D K hKD, equilibriumCharge, if_pos hv]
  calc
    _ = ∑ y ∈ D \ K, f y * ((1 / 4 : ℝ) *
        ∑ d : Direction, if y + step d = v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [he y hy]
    _ = (1 / 4 : ℝ) * ∑ d : Direction, f (v + step d) := hh
    _ = _ := by
      simp_rw [hn]
      rw [Finset.sum_sub_distrib, mul_sub]
      norm_num [Direction]

end SRWTightness
