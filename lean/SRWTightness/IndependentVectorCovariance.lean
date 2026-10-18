import SRWTightness.LinearObservationCovariance
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Total coordinate covariance of independent vector summands is the sum of their covariances. -/
theorem independent_vector_covariance_sum {Ω κ ι : Type*} [MeasurableSpace Ω]
    [Fintype κ] [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : κ → Ω → EuclideanSpace ℝ ι) (hind : iIndepFun W μ)
    (hW : ∀ j, MemLp (W j) 2 μ) (r s : ι) :
    covariance (fun ω ↦ ∑ j, W j ω r) (fun ω ↦ ∑ j, W j ω s) μ =
      ∑ j, covariance (fun ω ↦ W j ω r) (fun ω ↦ W j ω s) μ := by
  classical
  have hi (j : κ) (i : ι) : MemLp (fun ω ↦ W j ω i) 2 μ := (hW j).eval_piLp i
  have hc (i j : κ) : covariance (fun ω ↦ W i ω r) (fun ω ↦ W j ω s) μ =
      if i = j then covariance (fun ω ↦ W i ω r) (fun ω ↦ W i ω s) μ else 0 := by
    by_cases hij : i = j
    · subst j; simp
    · rw [if_neg hij]
      have hproj := (hind.indepFun hij).comp
        (show Measurable (fun x : EuclideanSpace ℝ ι ↦ x r) by fun_prop)
        (show Measurable (fun x : EuclideanSpace ℝ ι ↦ x s) by fun_prop)
      exact hproj.covariance_eq_zero (hi i r) (hi j s)
  rw [covariance_fun_sum_fun_sum (fun j ↦ hi j r) (fun j ↦ hi j s)]
  calc
    _ = ∑ i, ∑ j, if i = j then covariance (fun ω ↦ W i ω r)
        (fun ω ↦ W i ω s) μ else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ ↦ hc i j)
    _ = _ := by simp

end SRWTightness
