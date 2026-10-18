import SRWTightness.SuffixSumEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace SRWTightness

/-- Uniform adjacent suffix moments imply uniform coordinate moments with factor four. -/
theorem suffix_coordinate_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (X : Ω → Fin n → ℝ) (hX : ∀ i, Measurable (fun ω ↦ X ω i))
    (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ k ≤ n, Integrable (fun ω ↦ suffixSum (X ω) k ^ 2) μ ∧
      (∫ ω, suffixSum (X ω) k ^ 2 ∂μ) ≤ M) (i : Fin n) :
    Integrable (fun ω ↦ X ω i ^ 2) μ ∧ (∫ ω, X ω i ^ 2 ∂μ) ≤ 4 * M := by
  have h1 := hs i.val (by omega)
  have h2 := hs (i.val + 1) (by omega)
  have hb (ω : Ω) : X ω i ^ 2 ≤
      2 * suffixSum (X ω) i.val ^ 2 + 2 * suffixSum (X ω) (i.val + 1) ^ 2 := by
    have hh := suffixSum_step (X ω) i
    rw [show X ω i = suffixSum (X ω) i.val - suffixSum (X ω) (i.val + 1) by linarith]
    nlinarith [sq_nonneg (suffixSum (X ω) i.val + suffixSum (X ω) (i.val + 1))]
  have hg := (h1.1.const_mul 2).add (h2.1.const_mul 2)
  have hi := hg.mono_nonneg ((hX i).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ sq_nonneg _)) (Filter.Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hg hb
  simp only [Pi.add_apply] at hh
  rw [integral_add (h1.1.const_mul 2) (h2.1.const_mul 2),
    integral_const_mul, integral_const_mul] at hh
  linarith [h1.2, h2.2]

end SRWTightness
