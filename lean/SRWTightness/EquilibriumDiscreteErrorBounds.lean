import SRWTightness.EquilibriumEnergyOrder
import Mathlib.Algebra.Ring.GeomSum

namespace SRWTightness

/-- Converts a pointwise bound on the actual equilibrium probability weights into covariance loss. -/
theorem equilibriumDiscreteError_le_weight_bound (D K : Finset Site)
    (hKD : K ⊆ D) (hne : K.Nonempty) (g M : ℝ) (hg : 0 < g)
    (hweight : ∀ x ∈ K, equilibriumWeight D K x ≤ M) :
    equilibriumDiscreteError D K g ≤ M / (2 * g) := by
  unfold equilibriumDiscreteError
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ x ∈ K, M * equilibriumWeight D K x := by
      apply Finset.sum_le_sum
      intro x hx
      have hh := mul_le_mul_of_nonneg_right (hweight x hx) (equilibriumWeight_nonneg D K x)
      simpa only [pow_two] using hh
    _ = M := by rw [← Finset.mul_sum, equilibriumWeight_sum D K hKD hne, mul_one]

theorem equilibriumDiscreteError_uniform_upper (D K : Finset Site) (hKD : K ⊆ D)
    (hne : K.Nonempty) (g : ℝ) (hg : 0 < g) :
    equilibriumDiscreteError D K g ≤ 1 / (2 * g) :=
  equilibriumDiscreteError_le_weight_bound D K hKD hne g 1 hg
    (fun x _ ↦ equilibriumWeight_le_one D K hKD hne x)

theorem half_geometric_sum_le_two (n : ℕ) : (∑ i : Fin n, (1 / 2 : ℝ) ^ i.val) ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hh := geom_sum_mul_neg (1 / 2 : ℝ) n
  have hn : 0 ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) _
  nlinarith

/-- The remaining analytic input is only the displayed pointwise weight estimate.
This theorem does not assume or assert that this estimate has been proved for disks. -/
theorem equilibriumDiscreteError_sum_le_of_geometric_weight {n : ℕ}
    (D : Finset Site) (K : Fin n → Finset Site)
    (hKD : ∀ i, K i ⊆ D) (hne : ∀ i, (K i).Nonempty)
    (g W : ℝ) (hg : 0 < g) (hW : 0 ≤ W)
    (hweight : ∀ i x, x ∈ K i → equilibriumWeight D (K i) x ≤ W * (1 / 2 : ℝ) ^ i.val) :
    (∑ i, equilibriumDiscreteError D (K i) g) ≤ W / g := by
  have hpoint (i : Fin n) : equilibriumDiscreteError D (K i) g ≤
      (W / (2 * g)) * (1 / 2 : ℝ) ^ i.val := by
    have hh := equilibriumDiscreteError_le_weight_bound D (K i) (hKD i) (hne i)
      g (W * (1 / 2 : ℝ) ^ i.val) hg (hweight i)
    convert hh using 1 <;> ring
  calc
    _ ≤ ∑ i, (W / (2 * g)) * (1 / 2 : ℝ) ^ i.val := Finset.sum_le_sum (fun i _ ↦ hpoint i)
    _ = (W / (2 * g)) * ∑ i : Fin n, (1 / 2 : ℝ) ^ i.val := (Finset.mul_sum _ _ _).symm
    _ ≤ (W / (2 * g)) * 2 :=
      mul_le_mul_of_nonneg_left (half_geometric_sum_le_two n) (by positivity)
    _ = W / g := by ring

end SRWTightness
