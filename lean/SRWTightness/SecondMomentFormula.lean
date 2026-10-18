import SRWTightness.SecondMomentFirstStep
import SRWTightness.GreenRepresentation

namespace SRWTightness

 theorem occupationSecondMoment_poisson (D : Finset Site) (w y z : Site) (hw : w ∈ D) :
    occupationSecondMoment D w y z - (1 / 4 : ℝ) *
      ∑ d : Direction, occupationSecondMoment D (w + step d) y z =
      (if w = y then killedGreen D y z else 0) +
      (if w = z then killedGreen D z y else 0) - (if w = y ∧ w = z then 1 else 0) := by
  have h := occupationSecondMoment_first_step D w y z hw
  have hy := killedGreen_first_step_sum D w y hw
  have hz := killedGreen_first_step_sum D w z hw
  by_cases hwy : w = y <;> by_cases hwz : w = z <;>
    simp_all <;> linarith

/-- Exact ordered-visit second moment, including the discrete simultaneous-visit correction. -/
theorem occupationSecondMoment_formula (D : Finset Site) (x y z : Site)
    (hy : y ∈ D) (hz : z ∈ D) :
    occupationSecondMoment D x y z = killedGreen D x y * killedGreen D y z +
      killedGreen D x z * killedGreen D z y - (if y = z then killedGreen D x y else 0) := by
  rw [green_representation D (fun w ↦ occupationSecondMoment D w y z)
    (fun w hw ↦ occupationSecondMoment_zero_of_not_mem D w y z hw) x]
  have he : (∑ w ∈ D, killedGreen D x w *
      (occupationSecondMoment D w y z - (1 / 4 : ℝ) *
        ∑ d : Direction, occupationSecondMoment D (w + step d) y z)) =
      ∑ w ∈ D, killedGreen D x w * ((if w = y then killedGreen D y z else 0) +
        (if w = z then killedGreen D z y else 0) - (if w = y ∧ w = z then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [occupationSecondMoment_poisson D w y z hw]
  rw [he]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  by_cases hyz : y = z
  · subst z
    simp [hy]
  · have hfalse (w : Site) : ¬ (w = y ∧ w = z) := by
      rintro ⟨hwy, hwz⟩
      exact hyz (hwy.symm.trans hwz)
    simp [hy, hz, hfalse, hyz]

end SRWTightness
