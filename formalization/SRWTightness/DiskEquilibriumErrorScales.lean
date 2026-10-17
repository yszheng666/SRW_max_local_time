import SRWTightness.EquilibriumWeightRadiusParameters
import SRWTightness.EquilibriumDiscreteErrorBounds

namespace SRWTightness

/-- Actual disk weights on dyadic radii have a summable, dimension-independent bound. -/
theorem equilibriumWeight_dyadic_upper (b : Site) (A R : ℝ) (hA : 4 ≤ A)
    (i : ℕ) (hsep : 2 * (A * 2 ^ i) ≤ R) (x : Site) :
    equilibriumWeight (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset (A * 2 ^ i))) x ≤
        (diskEquilibriumWeightConstant / A) * (1 / 2 : ℝ) ^ i := by
  have hp : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have ha : 4 ≤ A * (2 : ℝ) ^ i := by nlinarith
  have hh := equilibriumWeight_translated_radius_upper b (A * 2 ^ i) R ha hsep x
  have he : diskEquilibriumWeightConstant / (A * (2 : ℝ) ^ i) =
      (diskEquilibriumWeightConstant / A) * (1 / 2 : ℝ) ^ i := by
    rw [one_div_pow, div_mul_eq_div_mul_one_div]
  rwa [he] at hh

theorem equilibriumDiscreteError_dyadic_sum_upper {n : ℕ} (b : Site) (A R g : ℝ)
    (hA : 4 ≤ A) (hg : 0 < g) (hsep : ∀ i : Fin n, 2 * (A * 2 ^ i.val) ≤ R) :
    (∑ i : Fin n, equilibriumDiscreteError (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset (A * 2 ^ i.val))) g) ≤
        (diskEquilibriumWeightConstant / A) / g := by
  have ha (i : Fin n) : 0 < A * (2 : ℝ) ^ i.val := by positivity
  have hKD (i : Fin n) : translateFinset b (diskFinset (A * 2 ^ i.val)) ⊆
      translateFinset b (diskFinset R) := by
    apply Finset.image_subset_image
    exact diskFinset_mono _ _ (ha i).le (by linarith [hsep i, ha i])
  have hne (i : Fin n) : (translateFinset b (diskFinset (A * 2 ^ i.val))).Nonempty :=
    Finset.Nonempty.image ⟨0, zero_mem_diskFinset _ (ha i)⟩ _
  exact equilibriumDiscreteError_sum_le_of_geometric_weight _ _ hKD hne g _ hg
    (div_nonneg diskEquilibriumWeightConstant_pos.le (by linarith))
    (fun i x _ ↦ equilibriumWeight_dyadic_upper b A R hA i.val (hsep i) x)

end SRWTightness
