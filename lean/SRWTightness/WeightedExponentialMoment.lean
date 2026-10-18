import SRWTightness.SixthMomentFromExponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

open MeasureTheory

namespace SRWTightness

/-- Finite probability-weighted averages preserve a common exponential-moment bound.
No independence between the coordinates is assumed. -/
theorem weighted_exponential_moment {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (s C : ℝ)
    (hi : ∀ i, Integrable (fun ω ↦ Real.exp (s * X i ω)) μ)
    (hb : ∀ i, (∫ ω, Real.exp (s * X i ω) ∂μ) ≤ C) :
    Integrable (fun ω ↦ Real.exp (s * ∑ i, w i * X i ω)) μ ∧
    (∫ ω, Real.exp (s * ∑ i, w i * X i ω) ∂μ) ≤ C := by
  have hdom (ω : Ω) : Real.exp (s * ∑ i, w i * X i ω) ≤
      ∑ i, w i * Real.exp (s * X i ω) := by
    have hh := convexOn_exp.map_sum_le (t := Finset.univ) (w := w)
      (p := fun i ↦ s * X i ω) (fun i _ ↦ hw i) hsum (fun _ _ ↦ Set.mem_univ _)
    simpa only [smul_eq_mul, Finset.mul_sum, mul_left_comm] using hh
  have hiB : Integrable (fun ω ↦ ∑ i, w i * Real.exp (s * X i ω)) μ :=
    integrable_finsetSum _ (fun i _ ↦ (hi i).const_mul (w i))
  have hm : Measurable (fun ω ↦ Real.exp (s * ∑ i, w i * X i ω)) := by
    fun_prop
  have hiA : Integrable (fun ω ↦ Real.exp (s * ∑ i, w i * X i ω)) μ :=
    hiB.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hdom ω))
  refine ⟨hiA, ?_⟩
  calc
    _ ≤ ∫ ω, ∑ i, w i * Real.exp (s * X i ω) ∂μ := integral_mono hiA hiB hdom
    _ = ∑ i, w i * (∫ ω, Real.exp (s * X i ω) ∂μ) := by
      rw [integral_finsetSum _ (fun i _ ↦ (hi i).const_mul (w i))]
      simp_rw [integral_const_mul]
    _ ≤ ∑ i, w i * C := Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = C := by rw [← Finset.sum_mul, hsum, one_mul]

end SRWTightness
