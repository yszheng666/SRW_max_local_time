import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace SRWTightness

/-- The cubic root-layer majorant is summable under the source exponential damping. -/
theorem upper_root_layer_cubic_summable :
    Summable (fun k : ℕ ↦ ((k : ℝ) + 1) ^ 3 * Real.exp (-(9 / 8 : ℝ) * k)) := by
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 9 / 8)
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 9 / 8)
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 9 / 8)
  have h3 := Real.summable_pow_mul_exp_neg_nat_mul 3 (by norm_num : (0 : ℝ) < 9 / 8)
  exact (((h3.add (h2.mul_left 3)).add (h1.mul_left 3)).add h0).congr
    (fun k ↦ by ring)

/-- The root-layer series in (4.33) has a uniform linear excess-height prefactor. -/
theorem upper_root_layer_series :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
      Summable (fun k : ℕ ↦ (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
        Real.exp (-(9 / 8 : ℝ) * k)) ∧
      (∑' k : ℕ, (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
        Real.exp (-(9 / 8 : ℝ) * k)) ≤ C * (1 + s) := by
  let f := fun k : ℕ ↦ ((k : ℝ) + 1) ^ 3 * Real.exp (-(9 / 8 : ℝ) * k)
  have hf : Summable f := upper_root_layer_cubic_summable
  have hf0 (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hsum0 : 0 ≤ ∑' k : ℕ, f k := tsum_nonneg hf0
  refine ⟨5 * ((∑' k : ℕ, f k) + 1), by positivity, ?_⟩
  intro s hs
  let g := fun k : ℕ ↦ (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
    Real.exp (-(9 / 8 : ℝ) * k)
  have hg0 (k : ℕ) : 0 ≤ g k := by dsimp [g]; positivity
  have hpoint (k : ℕ) : g k ≤ (5 * (1 + s)) * f k := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hlin : 5 + s + (k : ℝ) ≤ 5 * (1 + s) * ((k : ℝ) + 1) := by
      nlinarith [mul_nonneg hs hk]
    have hh := mul_le_mul_of_nonneg_right hlin
      (by positivity : 0 ≤ ((k : ℝ) + 1) ^ 2 * Real.exp (-(9 / 8 : ℝ) * k))
    dsimp [g, f]
    convert hh using 1 <;> first | rfl | ring
  have hg : Summable g := Summable.of_nonneg_of_le hg0 hpoint (hf.mul_left _)
  refine ⟨hg, ?_⟩
  have hh := hg.tsum_le_tsum hpoint (hf.mul_left (5 * (1 + s)))
  rw [tsum_mul_left] at hh
  change (∑' k : ℕ, g k) ≤ _
  nlinarith

end SRWTightness
