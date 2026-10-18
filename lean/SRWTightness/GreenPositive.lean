import SRWTightness.ReferenceLinearMoment
import SRWTightness.ObservationGreen
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix MeasureTheory

namespace SRWTightness

/-- Discrete visits give the stronger lower bound G ≥ I/2 as quadratic forms. -/
theorem observationGreen_quadratic_lower (D A : Finset Site) (hAD : A ⊆ D) (u : A → ℝ) :
    (∑ z : A, (u z) ^ 2) ≤ 2 * (∑ y : A, ∑ z : A, u y * killedGreen D y z * u z) := by
  let α := (capacity D A + 1)⁻¹
  have hc := capacity_nonneg D A
  have hp : 0 < capacity D A + 1 := by linarith
  have hα : 0 < α := inv_pos.mpr hp
  have hcap : α * capacity D A ≤ 1 := by
    dsimp [α]
    rw [inv_mul_eq_div]
    exact (div_le_one hp).mpr (by linarith)
  have he := referenceMark_linear_second_moment D A hAD α hα.le hcap u
  have hn : 0 ≤ ∫ Y : Mark A, (∑ z : A, u z * (Y z : ℝ)) ^ 2 ∂referenceMarkLaw D A α :=
    integral_nonneg (fun Y ↦ sq_nonneg _)
  rw [he] at hn
  nlinarith

 theorem observationGreen_posDef (D A : Finset Site) (hAD : A ⊆ D) :
    (observationGreen D A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro y z
    simpa only [star_trivial, observationGreen] using
      killedGreen_symm D z y (hAD z.property) (hAD y.property)
  · intro u hu
    have hex : ∃ z : A, u z ≠ 0 := by
      by_contra! h
      apply hu
      funext z
      exact h z
    obtain ⟨z, hz⟩ := hex
    have hs : 0 < ∑ z : A, (u z) ^ 2 :=
      (Finset.sum_pos_iff_of_nonneg (fun w _ ↦ sq_nonneg (u w))).mpr
        ⟨z, Finset.mem_univ _, sq_pos_of_ne_zero hz⟩
    have hl := observationGreen_quadratic_lower D A hAD u
    have hq : 0 < ∑ y : A, ∑ z : A, u y * killedGreen D y z * u z := by linarith
    simpa only [Matrix.mulVec, dotProduct, observationGreen, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc] using hq

 theorem greenMatrix_posDef (D : Finset Site) : (greenMatrix D).PosDef :=
  observationGreen_posDef D D (Finset.Subset.refl D)

end SRWTightness
