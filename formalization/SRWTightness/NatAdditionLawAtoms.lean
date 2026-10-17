import SRWTightness.GeometricGWGenerationCons
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.BigOperators.NatAntidiagonal

open MeasureTheory

namespace SRWTightness

/-- The atom of an independent natural-number sum is its finite convolution. -/
theorem nat_addition_law_atom (μ ν : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : ℕ) :
    ((μ.prod ν).map (fun p ↦ p.1 + p.2)).real {m} =
      ∑ i ∈ Finset.range (m + 1), μ.real {i} * ν.real {m - i} := by
  have hpre : (fun p : ℕ × ℕ ↦ p.1 + p.2) ⁻¹' {m} =
      (Finset.antidiagonal m : Set (ℕ × ℕ)) := by
    ext p
    simp
  rw [measureReal_def, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton m), hpre]
  change (μ.prod ν).real (Finset.antidiagonal m : Set (ℕ × ℕ)) = _
  rw [← sum_measureReal_singleton]
  calc
    _ = ∑ p ∈ Finset.antidiagonal m, μ.real {p.1} * ν.real {p.2} := by
      apply Finset.sum_congr rfl
      intro p hp
      have he : ({p} : Set (ℕ × ℕ)) = ({p.1} : Set ℕ) ×ˢ {p.2} := by
        ext q
        simp [Prod.ext_iff]
      rw [he, measureReal_prod_prod]
    _ = _ := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ μ.real {i} * ν.real {j}) m

/-- A geometric generation with one more parent has the exact finite convolution atoms. -/
theorem geometric_gw_generation_cons_atom (k m : ℕ) :
    (geometricGWGenerationLaw (k + 1)).real {m} =
      ∑ i ∈ Finset.range (m + 1), (1 / 2 : ℝ) ^ (i + 1) *
        (geometricGWGenerationLaw k).real {m - i} := by
  rw [geometric_gw_generation_cons, nat_addition_law_atom]
  simp_rw [geometricGWOffspringLaw_singleton]

end SRWTightness
