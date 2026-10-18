import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith

open Matrix

namespace SRWTightness

theorem eigenvalues_bounds_of_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (c C : ℝ)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x))
    (hhi : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ C * (∑ i, x i ^ 2)) (i : ι) :
    c ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ C := by
  let v : ι → ℝ := fun j ↦ hA.eigenvectorBasis i j
  have hv : ∃ j, v j ≠ 0 := by
    by_contra! hh
    have hz : hA.eigenvectorBasis i = 0 := by
      ext j
      exact hh j
    exact hA.eigenvectorBasis.orthonormal.ne_zero i hz
  obtain ⟨j, hj⟩ := hv
  have hs : 0 < ∑ j, v j ^ 2 :=
    (Finset.sum_pos_iff_of_nonneg (fun k _ ↦ sq_nonneg (v k))).mpr
      ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero hj⟩
  have he : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
  have hq : v ⬝ᵥ (A *ᵥ v) = hA.eigenvalues i * ∑ j, v j ^ 2 := by
    rw [he]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hl := hlo v
  have hu := hhi v
  rw [hq] at hl hu
  constructor <;> nlinarith

end SRWTightness
