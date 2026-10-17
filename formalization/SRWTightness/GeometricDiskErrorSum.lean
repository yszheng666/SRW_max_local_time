import SRWTightness.GeometricDiskWeightBounds
import Mathlib.Data.Fin.Rev

namespace SRWTightness

theorem equilibriumDiscreteError_geometric_sum_upper {n : ℕ} (b : Site) (A R q g : ℝ)
    (hA : 4 ≤ A) (hq : 2 ≤ q) (hg : 0 < g)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R) :
    (∑ i : Fin n, equilibriumDiscreteError (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset (A * q ^ i.val))) g) ≤
        (diskEquilibriumWeightConstant / A) / g := by
  have hA0 : 0 < A := by linarith
  have hq0 : 0 < q := by linarith
  have ha (i : Fin n) : 0 < A * q ^ i.val := by positivity
  have hKD (i : Fin n) : translateFinset b (diskFinset (A * q ^ i.val)) ⊆
      translateFinset b (diskFinset R) := by
    apply Finset.image_subset_image
    exact diskFinset_mono _ _ (ha i).le (by linarith [hsep i, ha i])
  have hne (i : Fin n) : (translateFinset b (diskFinset (A * q ^ i.val))).Nonempty :=
    Finset.Nonempty.image ⟨0, zero_mem_diskFinset _ (ha i)⟩ _
  exact equilibriumDiscreteError_sum_le_of_geometric_weight _ _ hKD hne g _ hg
    (div_nonneg diskEquilibriumWeightConstant_pos.le hA0.le)
    (fun i x _ ↦ equilibriumWeight_geometric_ratio_upper b A R q hA hq i.val (hsep i) x)

/-- Errors in increasing-time order, with zero error at the added center point. -/
noncomputable def geometricDiskPointError (b : Site) (A R q g : ℝ) (n : ℕ)
    (i : Fin (n + 1)) : ℝ :=
  if i.val < n then equilibriumDiscreteError (translateFinset b (diskFinset R))
    (translateFinset b (diskFinset (A * q ^ (n - 1 - i.val)))) g else 0

theorem geometricDiskPointError_nonneg (b : Site) (A R q g : ℝ) (hg : 0 ≤ g)
    (n : ℕ) (i : Fin (n + 1)) : 0 ≤ geometricDiskPointError b A R q g n i := by
  unfold geometricDiskPointError
  split_ifs
  · exact equilibriumDiscreteError_nonneg _ _ g hg
  · exact le_rfl

theorem geometricDiskPointError_sum (b : Site) (A R q g : ℝ) (n : ℕ) :
    (∑ i : Fin (n + 1), geometricDiskPointError b A R q g n i) =
      ∑ i : Fin n, equilibriumDiscreteError (translateFinset b (diskFinset R))
        (translateFinset b (diskFinset (A * q ^ i.val))) g := by
  rw [Fin.sum_univ_castSucc]
  simp only [geometricDiskPointError, Fin.val_castSucc, Fin.isLt, ↓reduceIte,
    Fin.val_last, lt_self_iff_false, add_zero]
  have he (i : Fin n) : n - 1 - i.val = i.rev.val := by rw [Fin.val_rev]; omega
  simp_rw [he]
  exact Equiv.sum_comp (Fin.revPerm : Fin n ≃ Fin n) (fun i : Fin n ↦ equilibriumDiscreteError
    (translateFinset b (diskFinset R)) (translateFinset b (diskFinset (A * q ^ i.val))) g)

end SRWTightness
