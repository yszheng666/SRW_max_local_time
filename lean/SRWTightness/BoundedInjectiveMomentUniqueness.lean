import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

open MeasureTheory BoundedContinuousFunction
namespace SRWTightness

/-- Powers of one bounded continuous injective coordinate determine a finite measure. -/
theorem bounded_injective_moment_uniqueness {E : Type*} [TopologicalSpace E]
    [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : E →ᵇ ℝ) (hf : Function.Injective f)
    (hm : ∀ n : ℕ, (∫ x, f x ^ n ∂μ) = ∫ x, f x ^ n ∂ν) : μ = ν := by
  let A : StarSubalgebra ℝ (E →ᵇ ℝ) :=
    { (Polynomial.aeval f).range with
      star_mem' := by
        intro g hg
        have he : star g = g := by ext x; simp
        rw [he]
        exact hg }
  have hpoly (p : Polynomial ℝ) :
      (∫ x, (Polynomial.aeval f p) x ∂μ) = ∫ x, (Polynomial.aeval f p) x ∂ν := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      simp only [map_add, coe_add, Pi.add_apply]
      rw [integral_add ((Polynomial.aeval f p).integrable (μ := μ))
          ((Polynomial.aeval f r).integrable (μ := μ)),
        integral_add ((Polynomial.aeval f p).integrable (μ := ν))
          ((Polynomial.aeval f r).integrable (μ := ν)),
        hp, hr]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, coe_mul, coe_pow, Pi.mul_apply, Pi.pow_apply,
        BoundedContinuousFunction.algebraMap_apply, smul_eq_mul, mul_one]
      rw [integral_const_mul, integral_const_mul, hm n]
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish (A := A)
  · intro x y hxy
    refine ⟨(toContinuousMapStarₐ ℝ) f, ?_, ?_⟩
    · exact ⟨(toContinuousMapStarₐ ℝ) f, ⟨f, ⟨Polynomial.X, by simp⟩, rfl⟩, rfl⟩
    · exact fun h ↦ hxy (hf h)
  · intro g hg
    obtain ⟨p, rfl⟩ := hg
    exact hpoly p

end SRWTightness
