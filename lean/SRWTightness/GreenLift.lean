import SRWTightness.GreenHarmonic

open Matrix

namespace SRWTightness

noncomputable def greenLift (D : Finset Site) (c : D → ℝ) (x : Site) : ℝ :=
  ∑ y : D, killedGreen D x y * c y

 theorem greenLift_zero_of_not_mem (D : Finset Site) (c : D → ℝ) (x : Site) (hx : x ∉ D) :
    greenLift D c x = 0 := by
  simp [greenLift, killedGreen_zero_of_not_mem D x _ hx]

 theorem greenLift_poisson (D : Finset Site) (c : D → ℝ) (x : D) :
    greenLift D c x - (1 / 4 : ℝ) * ∑ d : Direction, greenLift D c ((x : Site) + step d) = c x := by
  have he := congrFun (congrArg (fun A : Matrix D D ℝ ↦ A.mulVec c) (greenMatrix_right_inverse D)) x
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at he
  change greenLift D c x - (killedTransition D).mulVec (fun y : D ↦ greenLift D c y) x = c x at he
  rw [killedTransition_mulVec D _ (greenLift_zero_of_not_mem D c)] at he
  exact he

end SRWTightness
