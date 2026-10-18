import SRWTightness.GreenMatrix
import SRWTightness.DirectionReversal

open Matrix

namespace SRWTightness

 theorem killedTransition_symm (D : Finset Site) (x y : D) :
    killedTransition D x y = killedTransition D y x := by
  unfold killedTransition
  apply Fintype.sum_equiv directionReversal
  intro d
  have he : (y : Site) + step (directionReversal d) = (x : Site) ↔
      (x : Site) + step d = (y : Site) := by
    change (y : Site) + step (reverseDirection d) = (x : Site) ↔ _
    rw [step_reverseDirection, ← sub_eq_add_neg, sub_eq_iff_eq_add]
    exact eq_comm
  simp only [he]

 theorem killedTransition_transpose (D : Finset Site) :
    (killedTransition D)ᵀ = killedTransition D := by
  ext x y
  exact killedTransition_symm D y x

 theorem greenMatrix_transpose (D : Finset Site) : (greenMatrix D)ᵀ = greenMatrix D := by
  rw [greenMatrix_eq_inverse, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
    Matrix.transpose_one, killedTransition_transpose]

 theorem killedGreen_symm (D : Finset Site) (x y : Site) (hx : x ∈ D) (hy : y ∈ D) :
    killedGreen D x y = killedGreen D y x :=
  congrFun (congrFun (greenMatrix_transpose D) (⟨y, hy⟩ : D)) (⟨x, hx⟩ : D)

end SRWTightness
