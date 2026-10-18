import SRWTightness.WeightedMaximum
import SRWTightness.GreenHarmonic

open Matrix

namespace SRWTightness

noncomputable def extendZero (D : Finset Site) (v : D → ℝ) (x : Site) : ℝ :=
  if hx : x ∈ D then v ⟨x, hx⟩ else 0

@[simp] theorem extendZero_mem (D : Finset Site) (v : D → ℝ) (x : D) : extendZero D v x = v x := by
  simp [extendZero, x.property]

 theorem extendZero_not_mem (D : Finset Site) (v : D → ℝ) (x : Site) (hx : x ∉ D) :
    extendZero D v x = 0 := by simp [extendZero, hx]

noncomputable def weightedKilledMatrix (D : Finset Site) (v : D → ℝ) : Matrix D D ℝ :=
  1 - Matrix.diagonal v * killedTransition D

 theorem weightedKilledMatrix_isUnit (D : Finset Site) (v : D → ℝ)
    (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1) : IsUnit (weightedKilledMatrix D v) := by
  have hker (u : D → ℝ) (hu : (weightedKilledMatrix D v).mulVec u = 0) : u = 0 := by
    have hzero : extendZero D u = 0 := by
      apply weighted_harmonic_zero D _ (extendZero_not_mem D u)
      intro x hx
      let xx : D := ⟨x, hx⟩
      refine ⟨v xx, hv0 xx, hv1 xx, ?_⟩
      have he := congrFun hu xx
      simp only [weightedKilledMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Pi.sub_apply, Pi.mul_apply, Pi.zero_apply] at he
      have hu' : (fun y : D ↦ extendZero D u y) = u := by funext y; simp
      have hp := killedTransition_mulVec D (extendZero D u) (extendZero_not_mem D u) xx
      rw [hu'] at hp
      change extendZero D u xx = v xx * ((1 / 4 : ℝ) * ∑ d : Direction, extendZero D u ((xx : Site) + step d))
      rw [extendZero_mem, ← hp]
      linarith
    funext x
    have he := congrFun hzero x
    simpa using he
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u w huw
  have hz : (weightedKilledMatrix D v).mulVec (u - w) = 0 := by
    rw [Matrix.mulVec_sub, huw, sub_self]
  exact sub_eq_zero.mp (hker (u - w) hz)

end SRWTightness
