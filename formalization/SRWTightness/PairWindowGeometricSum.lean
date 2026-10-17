import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Three geometric window weights absorb the linear deficit factor with a uniform constant. -/
theorem pair_window_geometric_sum (r f : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hf : 0 ≤ f) :
    Summable (fun p : ℕ × ℕ × ℕ ↦
      r ^ p.1 * (r ^ p.2.1 * (r ^ p.2.2 * (f + p.2.2 + 1)))) ∧
    (∑' p : ℕ × ℕ × ℕ, r ^ p.1 * (r ^ p.2.1 * (r ^ p.2.2 * (f + p.2.2 + 1)))) ≤
      (f + 1) / (1 - r) ^ 4 := by
  have hg := hasSum_geometric_of_lt_one hr0 hr1
  have hrnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hm := hasSum_coe_mul_geometric_of_norm_lt_one hrnorm
  have hl : HasSum (fun l : ℕ ↦ r ^ l * (f + l + 1))
      ((f + 1) / (1 - r) + r / (1 - r) ^ 2) := by
    have hh : HasSum (fun l : ℕ ↦ r ^ l * (f + l + 1))
        ((f + 1) * (1 - r)⁻¹ + r / (1 - r) ^ 2) :=
      ((hg.mul_left (f + 1)).add hm).congr (fun l ↦ by dsimp; ring)
    simpa only [div_eq_mul_inv] using hh
  have hml := hg.summable.mul_of_nonneg hl.summable
    (fun _ ↦ pow_nonneg hr0 _) (fun l ↦ by positivity)
  have hall := hg.summable.mul_of_nonneg hml
    (fun _ ↦ pow_nonneg hr0 _) (fun p ↦ by positivity)
  refine ⟨hall, ?_⟩
  rw [← hg.summable.tsum_mul_tsum hml hall,
    ← hg.summable.tsum_mul_tsum hl.summable hml, hg.tsum_eq, hl.tsum_eq]
  have hd : 0 < 1 - r := by linarith
  have heq : (1 - r)⁻¹ * ((1 - r)⁻¹ * ((f + 1) / (1 - r) + r / (1 - r) ^ 2)) =
      (f + 1 - f * r) / (1 - r) ^ 4 := by
    field_simp [ne_of_gt hd]
    <;> ring
  rw [heq]
  exact div_le_div_of_nonneg_right (by nlinarith) (pow_nonneg hd.le 4)

end SRWTightness
