import SRWTightness.NaturalSecondMoment

open MeasureTheory

namespace SRWTightness

/-- A geometric tail controls positive generating parameters up to its convergence radius. -/
theorem integrable_pow_of_nat_geometric_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : Ω → ℕ) (hN : Measurable N)
    (C q b : ℝ) (hq0 : 0 ≤ q) (hb : 0 ≤ b) (hqb : q * b < 1)
    (ht : ∀ n : ℕ, μ.real {ω | n + 1 ≤ N ω} ≤ C * q ^ n) :
    Integrable (fun ω ↦ b ^ N ω) μ := by
  let ν := μ.map N
  have hm : AEStronglyMeasurable (fun n : ℕ ↦ b ^ n) ν :=
    (measurable_of_countable _).aestronglyMeasurable
  suffices hi : Integrable (fun n : ℕ ↦ b ^ n) ν from
    (integrable_map_measure hm hN.aemeasurable).mp hi
  have hbnd (n : ℕ) : ν.real {n + 1} ≤ C * q ^ n := by
    have he : ν.real {n + 1} = μ.real {ω | N ω = n + 1} := by
      unfold Measure.real ν
      rw [Measure.map_apply hN (measurableSet_singleton _)]
      rfl
    rw [he]
    exact (measureReal_mono (by intro ω hω; exact (show N ω = n + 1 from hω).symm.le)).trans (ht n)
  have hgeo : Summable (fun n : ℕ ↦ C * q ^ n * b ^ (n + 1)) := by
    have hnorm : ‖q * b‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq0 hb)]
    have hh := (summable_geometric_of_norm_lt_one hnorm).mul_left (C * b)
    exact hh.congr (fun n ↦ by rw [mul_pow, pow_succ]; ring)
  have hs : Summable (fun n : ℕ ↦ ν.real {n + 1} * b ^ (n + 1)) := by
    exact Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg measureReal_nonneg (pow_nonneg hb _))
      (fun n ↦ mul_le_mul_of_nonneg_right (hbnd n) (pow_nonneg hb _)) hgeo
  have hsall : Summable (fun n : ℕ ↦ ν.real {n} * b ^ n) :=
    (summable_nat_add_iff 1).mp hs
  rw [← Measure.sum_smul_dirac ν]
  apply integrable_sum_dirac (fun _ ↦ measure_ne_top _ _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hb _), Measure.real] using hsall

end SRWTightness
