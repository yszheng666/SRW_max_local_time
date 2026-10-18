import SRWTightness.Law
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory

namespace SRWTightness

 theorem summable_sq_succ_geometric (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (C : ℝ) :
    Summable (fun n : ℕ ↦ C * q ^ n * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hq : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have h0 := summable_geometric_of_norm_lt_one hq
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
  have hh : Summable (fun n : ℕ ↦ C * ((n : ℝ) ^ 2 * q ^ n +
      2 * ((n : ℝ) ^ 1 * q ^ n) + q ^ n)) := ((h2.add (h1.mul_left 2)).add h0).mul_left C
  exact hh.congr (fun n ↦ by push_cast; ring)

/-- A geometric upper tail gives the second moment needed before manipulating products. -/
theorem integrable_sq_of_nat_geometric_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : Ω → ℕ) (hN : Measurable N)
    (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ht : ∀ n : ℕ, μ.real {ω | n + 1 ≤ N ω} ≤ C * q ^ n) :
    Integrable (fun ω ↦ (N ω : ℝ) ^ 2) μ := by
  let ν := μ.map N
  have hm : AEStronglyMeasurable (fun n : ℕ ↦ (n : ℝ) ^ 2) ν :=
    (measurable_of_countable _).aestronglyMeasurable
  suffices hi : Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) ν from
    (integrable_map_measure hm hN.aemeasurable).mp hi
  have hb (n : ℕ) : ν.real {n + 1} ≤ C * q ^ n := by
    have he : ν.real {n + 1} = μ.real {ω | N ω = n + 1} := by
      unfold Measure.real ν
      rw [Measure.map_apply hN (measurableSet_singleton _)]
      rfl
    rw [he]
    exact (measureReal_mono (by intro ω hω; exact (show N ω = n + 1 from hω).symm.le)).trans (ht n)
  have hs : Summable (fun n : ℕ ↦ ν.real {n + 1} * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg measureReal_nonneg (sq_nonneg _))
      (fun n ↦ mul_le_mul_of_nonneg_right (hb n) (sq_nonneg _))
    exact summable_sq_succ_geometric q hq0 hq1 C
  have hsall : Summable (fun n : ℕ ↦ ν.real {n} * (n : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mp hs
  rw [← Measure.sum_smul_dirac ν]
  apply integrable_sum_dirac (fun _ ↦ measure_ne_top _ _)
  simpa only [Real.norm_eq_abs, abs_sq, Measure.real] using hsall

end SRWTightness
