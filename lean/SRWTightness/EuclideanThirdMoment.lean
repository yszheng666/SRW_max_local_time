import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory

namespace SRWTightness

/-- Coordinate third moments control the Euclidean third moment with the sharp dimension power. -/
theorem euclidean_norm_cube_le {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 3 ≤ Real.sqrt (Fintype.card ι) * ∑ i, |x i| ^ 3 := by
  have hp (t : ℝ) : (t ^ 2) ^ (3 / 2 : ℝ) = |t| ^ 3 := by
    rw [← sq_abs, ← Real.rpow_natCast (|t|) 2, ← Real.rpow_mul (abs_nonneg t)]
    norm_num
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := fun i ↦ (x i) ^ 2) (p := (3 / 2 : ℝ))
    (by norm_num) (fun i _ ↦ sq_nonneg (x i))
  rw [← EuclideanSpace.real_norm_sq_eq] at hh
  simp only [hp, abs_norm, Finset.card_univ] at hh
  norm_num only at hh
  simpa only [Real.sqrt_eq_rpow] using hh

/-- The Euclidean third moment is integrable whenever every coordinate third moment is. -/
theorem euclidean_third_moment_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ ι) (hX : Measurable X)
    (hi : ∀ i, Integrable (fun ω ↦ |X ω i| ^ 3) μ) :
    Integrable (fun ω ↦ ‖X ω‖ ^ 3) μ ∧
      (∫ ω, ‖X ω‖ ^ 3 ∂μ) ≤
        Real.sqrt (Fintype.card ι) * ∑ i, ∫ ω, |X ω i| ^ 3 ∂μ := by
  have hmajor : Integrable (fun ω ↦ Real.sqrt (Fintype.card ι) * ∑ i, |X ω i| ^ 3) μ :=
    (integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul _
  have hm : Measurable (fun ω ↦ ‖X ω‖ ^ 3) := by fun_prop
  have hnorm : Integrable (fun ω ↦ ‖X ω‖ ^ 3) μ :=
    hmajor.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact euclidean_norm_cube_le (X ω)))
  refine ⟨hnorm, ?_⟩
  have hh := integral_mono hnorm hmajor (fun ω ↦ euclidean_norm_cube_le (X ω))
  rwa [integral_const_mul, integral_finsetSum Finset.univ (fun i _ ↦ hi i)] at hh

end SRWTightness
