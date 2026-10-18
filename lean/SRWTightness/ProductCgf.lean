import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual moment generating function of a finite iid sum is the product of the factors. -/
theorem mgf_iid_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (k : ℕ) (s : ℝ) :
    mgf (fun Y : Fin k → Ω ↦ ∑ i, X (Y i)) (Measure.pi (fun _ : Fin k ↦ μ)) s =
      mgf X μ s ^ k := by
  simp only [mgf]
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin k ↦ fun x : Ω ↦ Real.exp (s * X x))]
  simp

/-- The cgf of a finite iid sum is the sum of the single-observation cgfs. -/
theorem cgf_iid_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (k : ℕ) (s : ℝ) :
    cgf (fun Y : Fin k → Ω ↦ ∑ i, X (Y i)) (Measure.pi (fun _ : Fin k ↦ μ)) s =
      k * cgf X μ s := by
  simp only [cgf, mgf_iid_sum, Real.log_pow]

/-- Exact cgf of the centered iid sum when the single exponential moment is finite. -/
theorem cgf_iid_centered_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (k : ℕ) (m : ℝ)
    (hi : Integrable (fun ω ↦ Real.exp (X ω)) μ) :
    cgf (fun Y : Fin k → Ω ↦ (∑ i, X (Y i)) - k * m)
      (Measure.pi (fun _ : Fin k ↦ μ)) 1 = k * (cgf X μ 1 - m) := by
  have hz : mgf X μ 1 ≠ 0 := (mgf_pos (by simpa only [one_mul] using hi)).ne'
  have hf : (fun Y : Fin k → Ω ↦ (∑ i, X (Y i)) - k * m) =
      (fun Y : Fin k → Ω ↦ (∑ i, X (Y i)) + (-(k : ℝ) * m)) := by
    funext Y
    ring
  rw [hf]
  simp only [cgf, mgf_add_const, mgf_iid_sum, one_mul]
  rw [Real.log_mul (pow_ne_zero _ hz) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
  ring

end SRWTightness
