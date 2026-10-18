import SRWTightness.ExponentialHolding
import SRWTightness.GeneratingFunction
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory

namespace SRWTightness

abbrev HoldingIndex {A : Finset Site} (Y : Mark A) := Σ z : A, Fin (Y z)
abbrev HoldingSample {A : Finset Site} (Y : Mark A) := HoldingIndex Y → ℝ

noncomputable def holdingTimeLaw {A : Finset Site} (Y : Mark A) : Measure (HoldingSample Y) :=
  Measure.pi (fun _ : HoldingIndex Y ↦ expMeasure 1)

instance holdingTimeLaw_isProbabilityMeasure {A : Finset Site} (Y : Mark A) :
    IsProbabilityMeasure (holdingTimeLaw Y) := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  unfold holdingTimeLaw
  infer_instance

noncomputable def continuousMark {A : Finset Site} (Y : Mark A) (T : HoldingSample Y) (z : A) : ℝ :=
  ∑ i : Fin (Y z), T ⟨z, i⟩

 theorem holdingVector_laplace {A : Finset Site} (Y : Mark A)
    (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∫ T, Real.exp (-(∑ z : A, f z * continuousMark Y T z)) ∂holdingTimeLaw Y) =
      markMonomial (fun z ↦ (1 + f z)⁻¹) Y := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have he (T : HoldingSample Y) : -(∑ z : A, f z * continuousMark Y T z) =
      ∑ j : HoldingIndex Y, -f j.1 * T j := by
    rw [Fintype.sum_sigma]
    simp only [continuousMark, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]
  simp_rw [he, Real.exp_sum]
  rw [holdingTimeLaw, integral_fintype_prod_eq_prod
    (f := fun (j : HoldingIndex Y) (t : ℝ) ↦ Real.exp (-f j.1 * t))]
  simp_rw [exponential_holding_laplace _ (hf _)]
  rw [Fintype.prod_sigma]
  simp [markMonomial]

end SRWTightness
