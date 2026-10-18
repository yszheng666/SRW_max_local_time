import SRWTightness.GreenFirstStep
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

namespace SRWTightness

noncomputable def killedTransition (D : Finset Site) : Matrix D D ℝ :=
  fun x y ↦ ∑ d : Direction, if (x : Site) + step d = (y : Site) then (1 / 4 : ℝ) else 0

noncomputable def greenMatrix (D : Finset Site) : Matrix D D ℝ :=
  fun x y ↦ killedGreen D x y

 theorem killedTransition_mul_green (D : Finset Site) (x y : D) :
    (killedTransition D * greenMatrix D) x y =
      (1 / 4 : ℝ) * ∑ d : Direction, killedGreen D ((x : Site) + step d) y := by
  simp only [Matrix.mul_apply, killedTransition, greenMatrix, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hn : (x : Site) + step d ∈ D
  · let z : D := ⟨(x : Site) + step d, hn⟩
    have he (w : D) : (x : Site) + step d = (w : Site) ↔ w = z := by
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        subst w
        rfl
    simp_rw [he]
    simp [z]
  · have he (w : D) : (x : Site) + step d ≠ (w : Site) := by
      intro h
      exact hn (h.symm ▸ w.property)
    simp [he, killedGreen_zero_of_not_mem D _ y hn]

 theorem greenMatrix_right_inverse (D : Finset Site) :
    (1 - killedTransition D) * greenMatrix D = 1 := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  ext x y
  have h := killedGreen_first_step_sum D x y x.property
  have hm := killedTransition_mul_green D x y
  have hi : (if (x : Site) = (y : Site) then (1 : ℝ) else 0) = (1 : Matrix D D ℝ) x y := by
    by_cases hxy : x = y
    · subst y
      simp only [Matrix.one_apply, if_pos rfl]
    · have hval : (x : Site) ≠ (y : Site) := fun h ↦ hxy (Subtype.ext h)
      simp only [Matrix.one_apply, if_neg hxy, if_neg hval]
  change killedGreen D x y - (killedTransition D * greenMatrix D) x y = _
  rw [← hi]
  linarith

/-- The probabilistic occupation kernel is exactly the finite killed-chain resolvent. -/
theorem greenMatrix_eq_inverse (D : Finset Site) :
    greenMatrix D = (1 - killedTransition D)⁻¹ :=
  (Matrix.inv_eq_right_inv (greenMatrix_right_inverse D)).symm

end SRWTightness
