import SRWTightness.NormalizedMarks

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem normalizedMarkSum_memLp_two (D A : Finset Site) (α g u : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (k : ℕ) (z : A) :
    MemLp (normalizedMarkSum A k α g u z) 2 (markProductLaw D A α k) := by
  letI := markProductLaw_isProbabilityMeasure D A α hα hcap k
  have hi : MemLp (fun Y : MarkSamples A k ↦ ∑ i : Fin k, (Y i z : ℝ)) 2
      (markProductLaw D A α k) :=
    memLp_finsetSum Finset.univ (fun i _ ↦ mark_coordinate_memLp_two D A α hα hcap k i z)
  change MemLp (fun Y : MarkSamples A k ↦ ((∑ i : Fin k, (Y i z : ℝ)) - α * k) /
    (u * Real.sqrt (α * g))) 2 (markProductLaw D A α k)
  simpa only [div_eq_mul_inv, Pi.sub_apply] using
    (hi.sub (memLp_const (α * k))).mul_const (u * Real.sqrt (α * g))⁻¹

noncomputable def normalizedWeightedSum (A : Finset Site) (k : ℕ) (α g u : ℝ)
    (w : A → ℝ) (Y : MarkSamples A k) : ℝ :=
  ∑ z : A, w z * normalizedMarkSum A k α g u z Y

theorem normalizedWeighted_covariance (D A : Finset Site) (hAD : A ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (w v : A → ℝ) :
    covariance (normalizedWeightedSum A k α g u w) (normalizedWeightedSum A k α g u v)
      (markProductLaw D A α k) =
      ∑ y : A, ∑ z : A, w y * v z *
        (killedGreen D y z / g - (if y = z then 1 else 0) / (2 * g) - α / (2 * g)) := by
  letI := markProductLaw_isProbabilityMeasure D A α hα.le hcap k
  unfold normalizedWeightedSum
  rw [covariance_fun_sum_fun_sum
    (fun z ↦ (normalizedMarkSum_memLp_two D A α g u hα.le hcap k z).const_mul (w z))
    (fun z ↦ (normalizedMarkSum_memLp_two D A α g u hα.le hcap k z).const_mul (v z))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    normalizedMarkSum_covariance D A hAD α g u hα hg hu hcap k hk, mul_assoc]

theorem weighted_covariance_algebra {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → ι → ℝ) (α g : ℝ) (w v : ι → ℝ)
    (hw : ∑ i, w i = 1) (hv : ∑ i, v i = 1) :
    (∑ y, ∑ z, w y * v z * (G y z / g - (if y = z then 1 else 0) / (2 * g) - α / (2 * g))) =
      (∑ y, ∑ z, w y * G y z * v z) / g - (∑ z, w z * v z) / (2 * g) - α / (2 * g) := by
  have ht (y z : ι) :
      w y * v z * (G y z / g - (if y = z then 1 else 0) / (2 * g) - α / (2 * g)) =
      (w y * G y z * v z) / g - (if y = z then w z * v z else 0) / (2 * g) -
        (α / (2 * g)) * (w y * v z) := by
    by_cases he : y = z
    · subst z; simp; ring
    · simp [he]; ring
  simp_rw [ht, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hc : (∑ y, ∑ z, α / (2 * g) * (w y * v z)) = α / (2 * g) := by
    simp_rw [← mul_assoc, ← Finset.mul_sum, hv, mul_one, ← Finset.mul_sum, hw, mul_one]
  rw [hc]

end SRWTightness
