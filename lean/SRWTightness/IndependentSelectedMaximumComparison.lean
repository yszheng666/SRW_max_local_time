import SRWTightness.GaussianHalfProbability
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory

namespace SRWTightness

def upperExceedanceOn {ι : Type*} (J : Finset ι) (t : ℝ) : Set (EuclideanSpace ℝ ι) := {x | ∃ i ∈ J, t ≤ x i}

theorem measurableSet_upperExceedanceOn {ι : Type*} [Fintype ι] (J : Finset ι) (t : ℝ) :
    MeasurableSet (upperExceedanceOn J t) := by
  unfold upperExceedanceOn
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i ∈ J
  · simp only [hi, true_and]
    exact measurableSet_le measurable_const (by fun_prop)
  · simp [hi]

/-- A symmetric independent perturbation loses at most a factor two in a maximum upper event. -/
theorem independent_maximum_on_comparison {ι : Type*} [Fintype ι]
    (μ ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : Finset ι) (hν : ∀ i, (1 / 2 : ℝ) ≤ ν.real {y | 0 ≤ y i}) (t : ℝ) :
    μ.real (upperExceedanceOn J t) ≤
      2 * ((μ.prod ν).map (fun p ↦ p.1 + p.2)).real (upperExceedanceOn J t) := by
  let E := upperExceedanceOn J t
  have hE : MeasurableSet E := measurableSet_upperExceedanceOn J t
  let S : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) := (fun p ↦ p.1 + p.2) ⁻¹' E
  have hS : MeasurableSet S := hE.preimage (by fun_prop)
  have hI : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (μ.prod ν) :=
    (integrable_const _).indicator hS
  have hpoint (x : EuclideanSpace ℝ ι) :
      E.indicator (fun _ ↦ (1 : ℝ)) x ≤
        2 * ∫ y, S.indicator (fun _ ↦ (1 : ℝ)) (x, y) ∂ν := by
    have hxS : MeasurableSet {y : EuclideanSpace ℝ ι | x + y ∈ E} :=
      hE.preimage (measurable_const_add x)
    have hi : (∫ y, S.indicator (fun _ ↦ (1 : ℝ)) (x, y) ∂ν) =
        ν.real {y : EuclideanSpace ℝ ι | x + y ∈ E} := by
      change (∫ y, {y : EuclideanSpace ℝ ι | x + y ∈ E}.indicator (fun _ ↦ (1 : ℝ)) y ∂ν) = _
      rw [integral_indicator_const _ hxS, smul_eq_mul, mul_one]
    rw [hi]
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      obtain ⟨i, hiJ, hi⟩ := hx
      have hm : ν.real {y | 0 ≤ y i} ≤ ν.real {y : EuclideanSpace ℝ ι | x + y ∈ E} := by
        apply measureReal_mono _ (measure_ne_top _ _)
        intro y hy
        change 0 ≤ y i at hy
        exact ⟨i, hiJ, by change t ≤ x i + y i; linarith⟩
      linarith [hν i]
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hm := integral_mono ((integrable_const (1 : ℝ)).indicator hE)
    (hI.integral_prod_left.const_mul 2) hpoint
  rw [integral_indicator_const _ hE, smul_eq_mul, mul_one, integral_const_mul,
    ← integral_prod _ hI, integral_indicator_const _ hS, smul_eq_mul, mul_one] at hm
  rw [map_measureReal_apply (by fun_prop) hE]
  exact hm

end SRWTightness
