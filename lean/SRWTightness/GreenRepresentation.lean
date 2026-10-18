import SRWTightness.GreenHarmonic

open Matrix

namespace SRWTightness

 theorem green_representation (D : Finset Site) (f : Site → ℝ)
    (hf : ∀ x, x ∉ D → f x = 0) (x : Site) :
    f x = ∑ y ∈ D, killedGreen D x y *
      (f y - (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) := by
  by_cases hx : x ∈ D
  · let xx : D := ⟨x, hx⟩
    have he : (1 - killedTransition D).mulVec (fun y : D ↦ f y) =
        (fun y : D ↦ f y - (1 / 4 : ℝ) * ∑ d : Direction, f ((y : Site) + step d)) := by
      funext y
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      change f y - (killedTransition D).mulVec (fun y : D ↦ f y) y = _
      rw [killedTransition_mulVec D f hf]
    have hm : (greenMatrix D).mulVec ((1 - killedTransition D).mulVec (fun y : D ↦ f y)) xx = f x := by
      rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp (greenMatrix_right_inverse D), Matrix.one_mulVec]
    rw [he] at hm
    rw [← Finset.sum_coe_sort D (fun y ↦ killedGreen D x y *
      (f y - (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)))]
    exact hm.symm
  · simp [hf x hx, killedGreen_zero_of_not_mem D x _ hx]

end SRWTightness
