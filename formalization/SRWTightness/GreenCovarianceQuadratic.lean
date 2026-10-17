import SRWTightness.NormalizedWeightedCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The discrete Green energy, diagonal correction and squared mean form the covariance quadratic. -/
theorem green_covariance_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → ι → ℝ) (α : ℝ) (β : ι → ℝ) :
    2 * α * (∑ y, ∑ z, β y * G y z * β z) - α * (∑ z, β z ^ 2) -
        (α * ∑ z, β z) ^ 2 =
      ∑ y, ∑ z, β y * β z * (2 * α * G y z - α * (if y = z then 1 else 0) - α ^ 2) := by
  have he (y z : ι) :
      β y * β z * (2 * α * G y z - α * (if y = z then 1 else 0) - α ^ 2) =
        2 * α * (β y * G y z * β z) - α * (if y = z then β z ^ 2 else 0) -
          α ^ 2 * (β y * β z) := by
    by_cases h : y = z
    · subst z; simp; ring
    · simp [h]; ring
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Finset.sum_mul]
  ring

/-- The Green-energy Taylor quadratic equals the actual normalized weighted covariance. -/
theorem normalized_green_quadratic_eq_covariance (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1) (w : K → ℝ)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let β := fun z ↦ w z / (u * Real.sqrt (α * g))
    k * (2 * α * (∑ y : K, ∑ z : K, β y * killedGreen D y z * β z) -
      α * (∑ z, β z ^ 2) - (α * ∑ z, β z) ^ 2) =
        covariance (normalizedWeightedSum K k α g u w) (normalizedWeightedSum K k α g u w)
          (markProductLaw D K α k) := by
  dsimp only
  rw [green_covariance_quadratic, normalizedWeighted_covariance D K hKD α g u hα hg hu hcap k hk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [← hk]
  calc
    _ = w y * w z * (((u ^ 2 / 2) *
      (2 * α * killedGreen D y z - α * (if y = z then 1 else 0) - α ^ 2)) /
        (u * Real.sqrt (α * g)) / (u * Real.sqrt (α * g))) := by ring
    _ = _ := by rw [normalized_covariance_algebra α g u _ _ hα hg hu]

end SRWTightness
