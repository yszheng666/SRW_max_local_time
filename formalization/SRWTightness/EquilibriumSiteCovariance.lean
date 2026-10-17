import SRWTightness.EquilibriumAverageCovariance
import SRWTightness.EquilibriumSupportSeparation

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem normalizedEquilibriumAverage_coordinate_covariance (D A K : Finset Site)
    (hKA : K ⊆ A) (hAD : A ⊆ D) (z : A) (hz : (z : Site) ∈ K)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    covariance (normalizedMarkSum A k α g u z)
      (normalizedEquilibriumAverage D A K k α g u) (markProductLaw D A α k) =
        1 / (g * capacity D K) - equilibriumWeight D K z / (2 * g) - α / (2 * g) := by
  letI := markProductLaw_isProbabilityMeasure D A α hα.le hcap k
  have hw : (∑ x : A, equilibriumWeight D K x) = 1 := by
    simpa only [Finset.sum_coe_sort] using equilibriumWeight_sum_over D A K hKA (hKA.trans hAD) ⟨z, hz⟩
  have hgreen : (∑ x : A, killedGreen D z x * equilibriumWeight D K x) = 1 / capacity D K := by
    rw [Finset.sum_coe_sort A (fun x ↦ killedGreen D z x * equilibriumWeight D K x)]
    exact equilibriumWeight_green_right_over D A K hKA hAD z hz
  unfold normalizedEquilibriumAverage normalizedWeightedSum
  rw [covariance_fun_sum_right
    (fun x ↦ (normalizedMarkSum_memLp_two D A α g u hα.le hcap k x).const_mul (equilibriumWeight D K x))
    (normalizedMarkSum_memLp_two D A α g u hα.le hcap k z)]
  simp_rw [covariance_const_mul_right, normalizedMarkSum_covariance D A hAD α g u hα hg hu hcap k hk]
  have ht (x : A) :
      equilibriumWeight D K x * (killedGreen D z x / g - (if z = x then 1 else 0) / (2 * g) - α / (2 * g)) =
      (killedGreen D z x * equilibriumWeight D K x) / g -
        (if z = x then equilibriumWeight D K x else 0) / (2 * g) -
        (α / (2 * g)) * equilibriumWeight D K x := by
    by_cases he : z = x
    · subst x; simp; ring
    · simp [he]; ring
  simp_rw [ht, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, hgreen, ← Finset.mul_sum, hw, mul_one]
  ring

theorem normalizedEquilibriumAverage_center_covariance (D A : Finset Site) (b : Site) (a : ℝ)
    (ha : 2 ≤ a) (hKA : translateFinset b (diskFinset a) ⊆ A) (hAD : A ⊆ D)
    (hb : b ∈ A) (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    covariance (normalizedMarkSum A k α g u ⟨b, hb⟩)
      (normalizedEquilibriumAverage D A (translateFinset b (diskFinset a)) k α g u)
      (markProductLaw D A α k) =
        1 / (g * capacity D (translateFinset b (diskFinset a))) - α / (2 * g) := by
  have hz : b ∈ translateFinset b (diskFinset a) := by
    rw [mem_translateFinset_iff, sub_self, mem_diskFinset]
    change normSq 0 < a ^ 2
    norm_num [normSq]
    nlinarith
  rw [normalizedEquilibriumAverage_coordinate_covariance D A _ hKA hAD ⟨b, hb⟩ hz
    α g u hα hg hu hcap k hk,
    translated_disk_equilibriumWeight_center_zero D b a ha (hKA.trans hAD), zero_div, sub_zero]

end SRWTightness
