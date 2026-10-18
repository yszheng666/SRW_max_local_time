import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

open MeasureTheory
namespace SRWTightness

/-- The two-to-one diagonal coordinate map of the real two-dimensional torus. -/
def diagonalTorusMap (T : ℝ) :
    (AddCircle T × AddCircle T) →+ (AddCircle T × AddCircle T) where
  toFun p := (p.1 + p.2, p.1 - p.2)
  map_zero' := by simp
  map_add' p q := by ext <;> simp <;> abel

/-- Every torus point has a diagonal-coordinate preimage. -/
theorem diagonalTorusMap_surjective (T : ℝ) : Function.Surjective (diagonalTorusMap T) := by
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨(((a + b) / 2 : ℝ), ((a - b) / 2 : ℝ)), ?_⟩
  apply Prod.ext
  · change (((a + b) / 2 : ℝ) : AddCircle T) + (((a - b) / 2 : ℝ) : AddCircle T) = _
    rw [← AddCircle.coe_add]
    congr 1
    ring
  · change (((a + b) / 2 : ℝ) : AddCircle T) - (((a - b) / 2 : ℝ) : AddCircle T) = _
    rw [← AddCircle.coe_sub]
    congr 1
    ring

/-- The diagonal coordinate map preserves the full torus Haar measure. -/
theorem diagonalTorusMap_measurePreserving (T : ℝ) [Fact (0 < T)] :
    MeasurePreserving (diagonalTorusMap T) volume volume := by
  change MeasurePreserving (diagonalTorusMap T)
    ((volume : Measure (AddCircle T)).prod volume)
    ((volume : Measure (AddCircle T)).prod volume)
  apply AddMonoidHom.measurePreserving
  · change Continuous (fun p : AddCircle T × AddCircle T ↦ (p.1 + p.2, p.1 - p.2))
    fun_prop
  · exact diagonalTorusMap_surjective T
  · rfl

/-- Measurable real torus integrals are invariant under the diagonal coordinate map. -/
theorem diagonalTorusMap_integral (T : ℝ) [Fact (0 < T)]
    (f : AddCircle T × AddCircle T → ℝ) (hf : Measurable f) :
    (∫ p, f (diagonalTorusMap T p)) = ∫ p, f p := by
  have hp := diagonalTorusMap_measurePreserving T
  have hi := integral_map (μ := (volume : Measure (AddCircle T × AddCircle T)))
    hp.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

end SRWTightness
