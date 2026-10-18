import SRWTightness.BrownianDiagonalPerturbation

open Matrix

namespace SRWTightness

noncomputable def brownianTimeMatrix (T : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  .of fun i j ↦ min (T (i.val + 1)) (T (j.val + 1))

theorem incrementTime_of_differences (T : ℕ → ℝ) (hT : T 0 = 0) (n : ℕ) (i : Fin n) :
    incrementTime (fun k : Fin n ↦ T (k.val + 1) - T k.val) i = T (i.val + 1) := by
  change (∑ k : Fin n, if k.val ≤ i.val then T (k.val + 1) - T k.val else 0) = T (i.val + 1)
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ if k ≤ i.val then T (k + 1) - T k else 0)]
  have he : (∑ k ∈ Finset.range n, if k ≤ i.val then T (k + 1) - T k else 0) =
      ∑ k ∈ Finset.range (i.val + 1), (T (k + 1) - T k) := by
    calc
      _ = ∑ k ∈ Finset.range (i.val + 1), if k ≤ i.val then T (k + 1) - T k else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt i.isLt))
        intro k hk hn
        have hh : ¬ k ≤ i.val := by simp only [Finset.mem_range] at hn; omega
        simp only [hh, ↓reduceIte]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hh : k ≤ i.val := by have := Finset.mem_range.mp hk; omega
        simp only [hh, ↓reduceIte]
  rw [he, Finset.sum_range_sub, hT, sub_zero]

theorem brownianTimeMatrix_eq_increment (T : ℕ → ℝ) (hT : T 0 = 0) (n : ℕ)
    (hmono : ∀ k < n, T k ≤ T (k + 1)) :
    brownianTimeMatrix T n = incrementCovariance (fun k : Fin n ↦ T (k.val + 1) - T k.val) := by
  ext i j
  rw [incrementCovariance_eq_min _ (fun k ↦ sub_nonneg.mpr (hmono k.val k.isLt)),
    incrementTime_of_differences T hT n i, incrementTime_of_differences T hT n j]
  rfl

/-- A quantitative Brownian covariance bound for arbitrary increasing observation times. -/
theorem brownianTimeMatrix_quadratic_lower (T : ℕ → ℝ) (hT : T 0 = 0) (n : ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hgap : ∀ k < n, δ ≤ T (k + 1) - T k) (x : Fin n → ℝ) :
    (δ / 4) * (∑ i, x i ^ 2) ≤ ∑ i, ∑ j, x i * brownianTimeMatrix T n i j * x j := by
  rw [brownianTimeMatrix_eq_increment T hT n (fun k hk ↦ by linarith [hgap k hk])]
  exact incrementCovariance_quadratic_lower _ x δ hδ (fun i ↦ hgap i.val i.isLt)

theorem brownianTimeMatrix_sub_diagonal_posDef (T : ℕ → ℝ) (hT : T 0 = 0) (n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ k < n, δ ≤ T (k + 1) - T k) (e : Fin n → ℝ)
    (he : ∀ i, e i ≤ δ / 8) : (brownianTimeMatrix T n - Matrix.diagonal e).PosDef := by
  rw [brownianTimeMatrix_eq_increment T hT n (fun k hk ↦ by linarith [hgap k hk])]
  exact incrementCovariance_sub_diagonal_posDef _ e δ hδ (fun i ↦ hgap i.val i.isLt) he

end SRWTightness
